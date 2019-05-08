#ifndef THREAD_POOL
#define THREAD_POOL


// the constructor just launches some amount of workers
inline ThreadPool::ThreadPool(size_t threads) : stop(false)
{
	runner = threads;
	for (size_t i = 0; i < threads; ++i){
		workers.emplace_back(
			[this]
				{
					for (;;)
					{
						std::function<void()> task;
						{
							std::unique_lock<std::mutex> lock(this->queue_mutex);
							runner -= 1;
							if (runner == 0) {
								wait_condition.notify_one();
							}
							this->condition.wait(lock, [this] { return this->stop || !this->tasks.empty(); });
							if (this->stop && this->tasks.empty())
								return;
							task = std::move(this->tasks.front());
							this->tasks.pop();
							runner += 1;
						}
						task();
					}
				}
		);
	}
}

template<class F, class... Args>
auto ThreadPool::enqueue(F&& f, Args&&... args)
{
	auto task = std::bind(std::forward<F>(f), std::forward<Args>(args)...);
	{
		std::unique_lock<std::mutex> lock(queue_mutex);
		tasks.emplace([task]() { (task)(); });
	}
	condition.notify_one();
}




inline void ThreadPool::wait() {
	for (;;) {
		{
			std::unique_lock<std::mutex> lock(this->queue_mutex);
			wait_condition.wait(lock, [this] { return this->tasks.empty(); });
			if (this->tasks.empty()&& !runner) {
				return;
			}
		}
	}

}


inline ThreadPool::~ThreadPool()
{
	{
		std::unique_lock<std::mutex> lock(queue_mutex);
		stop = true;
	}
	condition.notify_all();
	for (std::thread &worker : workers)
		worker.join();
	
}

#endif