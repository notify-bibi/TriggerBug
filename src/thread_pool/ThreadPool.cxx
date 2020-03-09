
#include "ThreadPool.h"

// the constructor just launches some amount of workers
ThreadPool::ThreadPool(size_t threads) : stop(false), runner(0)
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


void ThreadPool::wait() {
	std::unique_lock<std::mutex> lock(queue_mutex);
	wait_condition.wait(lock, [this] {
        //printf("??????? bk %d\n", !runner && this->tasks.empty());
        return !runner && this->tasks.empty();
        });
	return;
}


ThreadPool::~ThreadPool()
{
	{
		std::unique_lock<std::mutex> lock(queue_mutex);
		stop = true;
	}
	condition.notify_all();
	for (std::thread &worker : workers)
		worker.join();
	
}
