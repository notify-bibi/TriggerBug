#ifndef THREAD_POOL
#define THREAD_POOL


// the constructor just launches some amount of workers
inline ThreadPool::ThreadPool(size_t threads) : stop(false), runner(0)
{
	for (size_t i = 0; i < threads; ++i){
		workers.emplace_back(
			[this]
				{
					for (;;)
					{
						std::function<void()> task;
						{
							std::unique_lock<std::mutex> lock(this->queue_mutex);
							this->condition.wait(lock, [this] {
                                return this->stop || !this->tasks.empty();
                                });//成立就不阻塞
							if (this->stop && this->tasks.empty())
								return;
							task = std::move(this->tasks.front());
							this->tasks.pop();
                            runner++;
						}
						task();
                        bool beed_notify = false;
                        {
                            std::unique_lock<std::mutex> lock(this->queue_mutex);
                            runner--;
                            //printf("xxx: %d\n", runner);
                            if (!runner && this->tasks.empty()) {
                                beed_notify = true;
                            }
                        }
                        if (beed_notify) {
                            wait_condition.notify_one();
                        }
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
	std::unique_lock<std::mutex> lock(queue_mutex);
	wait_condition.wait(lock, [this] {
        //printf("??????? bk %d\n", !runner && this->tasks.empty());
        return !runner && this->tasks.empty();
        });
	return;
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