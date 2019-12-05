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
	auto enqueue(F&& f, Args&&... args);
	std::condition_variable condition; 
	std::condition_variable wait_condition;
	inline void wait();
	~ThreadPool();
	std::mutex main_mutex;
private:
	std::vector< std::thread > workers;
	std::queue< std::function<void()> > tasks;

	std::mutex queue_mutex;
	bool stop; 
    UInt runner;
};

#endif