/**
 * C++ 并发编程模式示例
 * 
 * 本文件演示现代C++中的并发编程模式：
 * - 线程池实现
 * - 生产者-消费者模式
 * - 读写锁模式
 * - Future/Promise模式
 */

#include <iostream>
#include <thread>
#include <mutex>
#include <condition_variable>
#include <queue>
#include <vector>
#include <future>
#include <functional>
#include <atomic>
#include <shared_mutex>
#include <chrono>
#include <random>

// ============================================
// 1. 线程池实现
// ============================================

class ThreadPool {
public:
    explicit ThreadPool(size_t num_threads = std::thread::hardware_concurrency())
        : stop_(false) {
        for (size_t i = 0; i < num_threads; ++i) {
            workers_.emplace_back([this, i] {
                // 设置线程名称（平台相关）
                std::cout << "工作线程 " << i << " 启动\n";
                
                while (true) {
                    std::function<void()> task;
                    
                    {
                        std::unique_lock<std::mutex> lock(queue_mutex_);
                        
                        // 等待任务或停止信号
                        condition_.wait(lock, [this] {
                            return stop_ || !tasks_.empty();
                        });
                        
                        // 检查是否需要退出
                        if (stop_ && tasks_.empty()) {
                            std::cout << "工作线程 " << i << " 退出\n";
                            return;
                        }
                        
                        // 获取任务
                        task = std::move(tasks_.front());
                        tasks_.pop();
                    }
                    
                    // 执行任务
                    task();
                }
            });
        }
    }
    
    ~ThreadPool() {
        {
            std::unique_lock<std::mutex> lock(queue_mutex_);
            stop_ = true;
        }
        condition_.notify_all();
        
        for (auto& worker : workers_) {
            worker.join();
        }
    }
    
    // 提交任务，返回future
    template<typename F, typename... Args>
    auto submit(F&& f, Args&&... args) -> std::future<std::invoke_result_t<F, Args...>> {
        using return_type = std::invoke_result_t<F, Args...>;
        
        // 包装任务
        auto task = std::make_shared<std::packaged_task<return_type()>>(
            std::bind(std::forward<F>(f), std::forward<Args>(args)...)
        );
        
        std::future<return_type> result = task->get_future();
        
        {
            std::unique_lock<std::mutex> lock(queue_mutex_);
            
            if (stop_) {
                throw std::runtime_error("线程池已停止");
            }
            
            tasks_.emplace([task]() { (*task)(); });
        }
        
        condition_.notify_one();
        return result;
    }
    
    // 获取待处理任务数
    size_t pendingTasks() const {
        std::unique_lock<std::mutex> lock(queue_mutex_);
        return tasks_.size();
    }
    
private:
    std::vector<std::thread> workers_;
    std::queue<std::function<void()>> tasks_;
    
    mutable std::mutex queue_mutex_;
    std::condition_variable condition_;
    bool stop_;
};

void demonstrate_thread_pool() {
    std::cout << "\n=== 线程池演示 ===\n";
    
    ThreadPool pool(4);
    
    std::vector<std::future<int>> results;
    
    // 提交多个任务
    for (int i = 0; i < 8; ++i) {
        results.push_back(pool.submit([i] {
            std::cout << "任务 " << i << " 在线程 " 
                      << std::this_thread::get_id() << " 执行\n";
            
            // 模拟工作
            std::this_thread::sleep_for(std::chrono::milliseconds(100));
            
            return i * i;
        }));
    }
    
    // 获取结果
    for (size_t i = 0; i < results.size(); ++i) {
        std::cout << "任务 " << i << " 结果: " << results[i].get() << "\n";
    }
}

// ============================================
// 2. 生产者-消费者模式
// ============================================

template<typename T>
class BlockingQueue {
public:
    explicit BlockingQueue(size_t capacity) : capacity_(capacity) {}
    
    // 生产者：添加元素
    void produce(T item) {
        std::unique_lock<std::mutex> lock(mutex_);
        
        // 等待队列有空间
        not_full_.wait(lock, [this] { return queue_.size() < capacity_; });
        
        queue_.push(std::move(item));
        not_empty_.notify_one();
    }
    
    // 消费者：取出元素
    T consume() {
        std::unique_lock<std::mutex> lock(mutex_);
        
        // 等待队列有元素
        not_empty_.wait(lock, [this] { return !queue_.empty(); });
        
        T item = std::move(queue_.front());
        queue_.pop();
        not_full_.notify_one();
        
        return item;
    }
    
    // 尝试消费（非阻塞）
    bool try_consume(T& item, std::chrono::milliseconds timeout) {
        std::unique_lock<std::mutex> lock(mutex_);
        
        if (!not_empty_.wait_for(lock, timeout, [this] { return !queue_.empty(); })) {
            return false;
        }
        
        item = std::move(queue_.front());
        queue_.pop();
        not_full_.notify_one();
        return true;
    }
    
    size_t size() const {
        std::unique_lock<std::mutex> lock(mutex_);
        return queue_.size();
    }
    
    void shutdown() {
        std::unique_lock<std::mutex> lock(mutex_);
        shutdown_ = true;
        not_empty_.notify_all();
        not_full_.notify_all();
    }
    
    bool is_shutdown() const {
        std::unique_lock<std::mutex> lock(mutex_);
        return shutdown_;
    }
    
private:
    std::queue<T> queue_;
    mutable std::mutex mutex_;
    std::condition_variable not_empty_;
    std::condition_variable not_full_;
    size_t capacity_;
    bool shutdown_ = false;
};

void demonstrate_producer_consumer() {
    std::cout << "\n=== 生产者-消费者模式演示 ===\n";
    
    BlockingQueue<int> queue(5);
    std::atomic<int> produced_count{0};
    std::atomic<int> consumed_count{0};
    
    // 生产者线程
    auto producer = [&queue, &produced_count](int id, int count) {
        std::random_device rd;
        std::mt19937 gen(rd());
        std::uniform_int_distribution<> delay(10, 50);
        
        for (int i = 0; i < count; ++i) {
            int value = id * 100 + i;
            queue.produce(value);
            ++produced_count;
            std::cout << "生产者 " << id << " 生产: " << value 
                      << " (队列大小: " << queue.size() << ")\n";
            std::this_thread::sleep_for(std::chrono::milliseconds(delay(gen)));
        }
    };
    
    // 消费者线程
    auto consumer = [&queue, &consumed_count](int id) {
        while (!queue.is_shutdown() || queue.size() > 0) {
            int value;
            if (queue.try_consume(value, std::chrono::milliseconds(100))) {
                ++consumed_count;
                std::cout << "消费者 " << id << " 消费: " << value 
                          << " (队列大小: " << queue.size() << ")\n";
            }
        }
    };
    
    // 启动线程
    std::thread p1(producer, 1, 5);
    std::thread p2(producer, 2, 5);
    std::thread c1(consumer, 1);
    std::thread c2(consumer, 2);
    
    // 等待生产者完成
    p1.join();
    p2.join();
    
    // 等待消费者处理完剩余数据
    std::this_thread::sleep_for(std::chrono::milliseconds(500));
    queue.shutdown();
    
    c1.join();
    c2.join();
    
    std::cout << "总计生产: " << produced_count << ", 消费: " << consumed_count << "\n";
}

// ============================================
// 3. 读写锁模式
// ============================================

template<typename T>
class ReadWriteProtected {
public:
    explicit ReadWriteProtected(T data) : data_(std::move(data)) {}
    
    // 读操作（共享锁）
    template<typename Func>
    auto read(Func&& func) const -> decltype(func(std::declval<const T&>())) {
        std::shared_lock<std::shared_mutex> lock(mutex_);
        return func(data_);
    }
    
    // 写操作（独占锁）
    template<typename Func>
    auto write(Func&& func) -> decltype(func(std::declval<T&>())) {
        std::unique_lock<std::shared_mutex> lock(mutex_);
        return func(data_);
    }
    
private:
    T data_;
    mutable std::shared_mutex mutex_;
};

void demonstrate_read_write_lock() {
    std::cout << "\n=== 读写锁模式演示 ===\n";
    
    ReadWriteProtected<std::vector<int>> protected_data(std::vector<int>{});
    std::atomic<int> read_count{0};
    std::atomic<int> write_count{0};
    
    // 写线程
    auto writer = [&protected_data, &write_count](int id, int count) {
        for (int i = 0; i < count; ++i) {
            protected_data.write([id, i, &write_count](std::vector<int>& data) {
                data.push_back(id * 100 + i);
                ++write_count;
                std::cout << "写者 " << id << " 写入: " << (id * 100 + i) 
                          << " (大小: " << data.size() << ")\n";
            });
            std::this_thread::sleep_for(std::chrono::milliseconds(50));
        }
    };
    
    // 读线程
    auto reader = [&protected_data, &read_count](int id, int iterations) {
        for (int i = 0; i < iterations; ++i) {
            protected_data.read([id, &read_count](const std::vector<int>& data) {
                ++read_count;
                std::cout << "读者 " << id << " 读取大小: " << data.size() << "\n";
            });
            std::this_thread::sleep_for(std::chrono::milliseconds(30));
        }
    };
    
    std::thread w1(writer, 1, 3);
    std::thread w2(writer, 2, 3);
    std::thread r1(reader, 1, 5);
    std::thread r2(reader, 2, 5);
    std::thread r3(reader, 3, 5);
    
    w1.join();
    w2.join();
    r1.join();
    r2.join();
    r3.join();
    
    std::cout << "总读取次数: " << read_count << ", 写入次数: " << write_count << "\n";
}

// ============================================
// 4. Future/Promise 模式
// ============================================

void demonstrate_future_promise() {
    std::cout << "\n=== Future/Promise 模式演示 ===\n";
    
    // 基本 future/promise
    {
        std::promise<int> promise;
        std::future<int> future = promise.get_future();
        
        std::thread worker([&promise] {
            std::cout << "工作者计算中...\n";
            std::this_thread::sleep_for(std::chrono::milliseconds(200));
            promise.set_value(42);
        });
        
        std::cout << "等待结果...\n";
        int result = future.get();
        std::cout << "结果: " << result << "\n";
        
        worker.join();
    }
    
    // 共享 future
    {
        std::promise<std::string> promise;
        std::shared_future<std::string> shared_future = promise.get_future().share();
        
        std::thread producer([&promise] {
            std::this_thread::sleep_for(std::chrono::milliseconds(100));
            promise.set_value("共享数据");
        });
        
        std::thread consumer1([shared_future] {
            std::cout << "消费者1: " << shared_future.get() << "\n";
        });
        
        std::thread consumer2([shared_future] {
            std::cout << "消费者2: " << shared_future.get() << "\n";
        });
        
        producer.join();
        consumer1.join();
        consumer2.join();
    }
    
    // async 启动策略
    {
        std::cout << "\nasync 策略演示:\n";
        
        // 延迟执行（调用get时才执行）
        auto lazy = std::async(std::launch::deferred, [] {
            std::cout << "延迟任务执行\n";
            return 1;
        });
        
        // 异步执行（立即在新线程执行）
        auto async_task = std::async(std::launch::async, [] {
            std::cout << "异步任务执行\n";
            return 2;
        });
        
        std::cout << "延迟结果: " << lazy.get() << "\n";
        std::cout << "异步结果: " << async_task.get() << "\n";
    }
}

// ============================================
// 5. 原子操作演示
// ============================================

void demonstrate_atomic() {
    std::cout << "\n=== 原子操作演示 ===\n";
    
    std::atomic<int> counter{0};
    std::atomic_flag lock = ATOMIC_FLAG_INIT;
    
    auto increment = [&counter](int iterations) {
        for (int i = 0; i < iterations; ++i) {
            counter.fetch_add(1, std::memory_order_relaxed);
        }
    };
    
    std::thread t1(increment, 10000);
    std::thread t2(increment, 10000);
    std::thread t3(increment, 10000);
    
    t1.join();
    t2.join();
    t3.join();
    
    std::cout << "最终计数: " << counter.load() << " (期望: 30000)\n";
    
    // 自旋锁示例
    auto spinlock_demo = [&lock](int id) {
        while (lock.test_and_set(std::memory_order_acquire)) {
            // 自旋等待
        }
        
        std::cout << "线程 " << id << " 获得锁\n";
        std::this_thread::sleep_for(std::chrono::milliseconds(50));
        std::cout << "线程 " << id << " 释放锁\n";
        
        lock.clear(std::memory_order_release);
    };
    
    std::thread s1(spinlock_demo, 1);
    std::thread s2(spinlock_demo, 2);
    
    s1.join();
    s2.join();
}

// ============================================
// 主函数
// ============================================

int main() {
    std::cout << "========================================\n";
    std::cout << "C++ 并发编程模式示例\n";
    std::cout << "========================================\n";
    
    demonstrate_thread_pool();
    demonstrate_producer_consumer();
    demonstrate_read_write_lock();
    demonstrate_future_promise();
    demonstrate_atomic();
    
    std::cout << "\n========================================\n";
    std::cout << "所有并发演示完成\n";
    std::cout << "========================================\n";
    
    return 0;
}
