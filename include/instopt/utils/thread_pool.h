#ifndef THREAD_POOL_H
#define THREAD_POOL_H

#include <vector>
#include <queue>
#include <memory>
#include <thread>
#include <mutex>
#include <condition_variable>
#include <future>
#include <functional>
#include <stdexcept>


class ThreadPool {
public:
	ThreadPool(size_t);
	template<class F, class... Args>
	void enqueue(F&& f, Args&&... args)
	{
		auto task = std::bind(std::forward<F>(f), std::forward<Args>(args)...);
		{
			std::unique_lock<std::mutex> lock(queue_mutex);
			tasks.emplace([task]() { (task)(); });
		}
		condition.notify_one();
	}

	void wait();
	~ThreadPool();
	std::mutex main_mutex;
private:
	std::condition_variable condition;
	std::condition_variable wait_condition;
	std::vector< std::thread > workers;
	std::queue< std::function<void()> > tasks;

	std::mutex queue_mutex;
	bool stop; 
    uint32_t runner;
};

#endif