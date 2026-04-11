/**
 * C++ 内存管理最佳实践示例
 * 
 * 本文件演示现代C++中的内存管理技术：
 * - 智能指针（RAII自动内存管理）
 * - 自定义删除器
 * - 内存池实现
 * - 避免内存泄漏的最佳实践
 */

#include <iostream>
#include <memory>
#include <vector>
#include <array>
#include <functional>

// ============================================
// 1. 智能指针基础示例
// ============================================

class Resource {
public:
    Resource(int id) : id_(id) {
        std::cout << "Resource " << id_ << " 构造\n";
    }
    
    ~Resource() {
        std::cout << "Resource " << id_ << " 析构\n";
    }
    
    void use() const {
        std::cout << "使用 Resource " << id_ << "\n";
    }
    
private:
    int id_;
};

// unique_ptr: 独占所有权
void demonstrate_unique_ptr() {
    std::cout << "\n=== unique_ptr 演示 ===\n";
    
    // 方式1: 直接构造
    std::unique_ptr<Resource> res1(new Resource(1));
    
    // 方式2: 推荐方式（更安全，异常安全）
    auto res2 = std::make_unique<Resource>(2);
    
    // 使用资源
    res1->use();
    res2->use();
    
    // 转移所有权
    std::unique_ptr<Resource> res3 = std::move(res1);
    // res1 现在为 nullptr
    
    if (!res1) {
        std::cout << "res1 已被转移，为空指针\n";
    }
    
    // 函数退出时，res2 和 res3 自动释放
}

// shared_ptr: 共享所有权
void demonstrate_shared_ptr() {
    std::cout << "\n=== shared_ptr 演示 ===\n";
    
    // 创建共享资源
    auto shared = std::make_shared<Resource>(100);
    std::cout << "引用计数: " << shared.use_count() << "\n";
    
    {
        // 复制shared_ptr，引用计数增加
        auto another = shared;
        std::cout << "复制后引用计数: " << shared.use_count() << "\n";
        another->use();
    } // another 离开作用域，引用计数减少
    
    std::cout << "出作用域后引用计数: " << shared.use_count() << "\n";
    
    // shared_ptr 存储在容器中
    std::vector<std::shared_ptr<Resource>> resources;
    resources.push_back(shared);
    resources.push_back(shared);
    std::cout << "存入容器后引用计数: " << shared.use_count() << "\n";
    
    // 容器清空时，引用计数自动减少
    resources.clear();
    std::cout << "清空容器后引用计数: " << shared.use_count() << "\n";
}

// weak_ptr: 弱引用，解决循环引用问题
void demonstrate_weak_ptr() {
    std::cout << "\n=== weak_ptr 演示 ===\n";
    
    struct Node {
        int value;
        std::shared_ptr<Node> next;      // 强引用 - 可能导致循环引用
        std::weak_ptr<Node> parent;       // 弱引用 - 打破循环
        
        Node(int v) : value(v) {
            std::cout << "Node " << value << " 创建\n";
        }
        ~Node() {
            std::cout << "Node " << value << " 销毁\n";
        }
    };
    
    // 创建节点
    auto node1 = std::make_shared<Node>(1);
    auto node2 = std::make_shared<Node>(2);
    
    // 建立连接：node1 -> node2
    node1->next = node2;
    // 反向连接使用 weak_ptr
    node2->parent = node1;
    
    std::cout << "node1 引用计数: " << node1.use_count() << "\n";
    std::cout << "node2 引用计数: " << node2.use_count() << "\n";
    
    // 使用 weak_ptr 前需要锁定
    if (auto locked = node2->parent.lock()) {
        std::cout << "父节点值: " << locked->value << "\n";
    }
    
    // 函数结束时正常销毁，无内存泄漏
}

// ============================================
// 2. 自定义删除器
// ============================================

void demonstrate_custom_deleter() {
    std::cout << "\n=== 自定义删除器演示 ===\n";
    
    // 文件句柄管理
    struct FileDeleter {
        void operator()(FILE* file) const {
            if (file) {
                std::cout << "关闭文件\n";
                fclose(file);
            }
        }
    };
    
    // 使用自定义删除器
    {
        std::unique_ptr<FILE, FileDeleter> file(
            fopen("test.txt", "w")
        );
        if (file) {
            std::cout << "写入文件...\n";
            fprintf(file.get(), "Hello, C++!\n");
        }
        // 文件自动关闭
    }
    
    // 使用 Lambda 作为删除器
    auto array_deleter = [](int* p) {
        std::cout << "删除数组\n";
        delete[] p;
    };
    
    std::unique_ptr<int, decltype(array_deleter)> arr(
        new int[100], 
        array_deleter
    );
}

// ============================================
// 3. 内存池实现
// ============================================

template<typename T, size_t BlockSize = 1024>
class MemoryPool {
public:
    MemoryPool() : free_list_(nullptr) {}
    
    ~MemoryPool() {
        // 释放所有块
        for (auto& block : blocks_) {
            delete[] block;
        }
    }
    
    // 禁止复制
    MemoryPool(const MemoryPool&) = delete;
    MemoryPool& operator=(const MemoryPool&) = delete;
    
    // 分配对象
    template<typename... Args>
    T* allocate(Args&&... args) {
        // 从空闲列表获取
        if (free_list_) {
            Node* node = free_list_;
            free_list_ = free_list_->next;
            T* obj = reinterpret_cast<T*>(node);
            new (obj) T(std::forward<Args>(args)...);
            return obj;
        }
        
        // 分配新块
        if (current_offset_ >= BlockSize) {
            allocateBlock();
        }
        
        char* block = blocks_.back();
        T* obj = reinterpret_cast<T*>(block + current_offset_ * sizeof(T));
        new (obj) T(std::forward<Args>(args)...);
        ++current_offset_;
        return obj;
    }
    
    // 释放对象（返回到池）
    void deallocate(T* obj) {
        obj->~T();
        Node* node = reinterpret_cast<Node*>(obj);
        node->next = free_list_;
        free_list_ = node;
    }
    
private:
    union Node {
        T data;
        Node* next;
    };
    
    void allocateBlock() {
        char* new_block = new char[BlockSize * sizeof(T)];
        blocks_.push_back(new_block);
        current_offset_ = 0;
    }
    
    std::vector<char*> blocks_;
    Node* free_list_;
    size_t current_offset_ = BlockSize; // 触发第一次分配
};

void demonstrate_memory_pool() {
    std::cout << "\n=== 内存池演示 ===\n";
    
    struct SmallObject {
        int x, y, z;
        SmallObject(int a, int b, int c) : x(a), y(b), z(c) {
            std::cout << "SmallObject 构造\n";
        }
        ~SmallObject() {
            std::cout << "SmallObject 析构\n";
        }
    };
    
    MemoryPool<SmallObject, 4> pool;
    
    // 从池中分配对象
    auto* obj1 = pool.allocate(1, 2, 3);
    auto* obj2 = pool.allocate(4, 5, 6);
    auto* obj3 = pool.allocate(7, 8, 9);
    
    std::cout << "对象值: (" << obj1->x << ", " << obj1->y << ", " << obj1->z << ")\n";
    
    // 释放回池中
    pool.deallocate(obj1);
    pool.deallocate(obj2);
    pool.deallocate(obj3);
    
    // 可以重新分配
    auto* obj4 = pool.allocate(10, 11, 12);
    std::cout << "重用后对象值: (" << obj4->x << ", " << obj4->y << ", " << obj4->z << ")\n";
    pool.deallocate(obj4);
}

// ============================================
// 4. RAII 封装示例
// ============================================

template<typename Lockable>
class ScopedLock {
public:
    explicit ScopedLock(Lockable& lock) : lock_(lock), locked_(true) {
        lock_.lock();
    }
    
    ~ScopedLock() {
        if (locked_) {
            lock_.unlock();
        }
    }
    
    // 禁止复制
    ScopedLock(const ScopedLock&) = delete;
    ScopedLock& operator=(const ScopedLock&) = delete;
    
    // 允许移动
    ScopedLock(ScopedLock&& other) noexcept 
        : lock_(other.lock_), locked_(other.locked_) {
        other.locked_ = false;
    }
    
    void unlock() {
        if (locked_) {
            lock_.unlock();
            locked_ = false;
        }
    }
    
    void lock() {
        if (!locked_) {
            lock_.lock();
            locked_ = true;
        }
    }
    
private:
    Lockable& lock_;
    bool locked_;
};

void demonstrate_raii() {
    std::cout << "\n=== RAII 模式演示 ===\n";
    
    // 使用 std::mutex 演示
    std::mutex mtx;
    
    {
        ScopedLock lock(mtx);
        std::cout << "获得锁，执行关键操作\n";
        // 锁会在离开作用域时自动释放
    }
    
    std::cout << "锁已释放\n";
}

// ============================================
// 主函数
// ============================================

int main() {
    std::cout << "========================================\n";
    std::cout << "C++ 内存管理最佳实践示例\n";
    std::cout << "========================================\n";
    
    demonstrate_unique_ptr();
    demonstrate_shared_ptr();
    demonstrate_weak_ptr();
    demonstrate_custom_deleter();
    demonstrate_memory_pool();
    demonstrate_raii();
    
    std::cout << "\n========================================\n";
    std::cout << "所有演示完成\n";
    std::cout << "========================================\n";
    
    return 0;
}
