# C++ 代码示例

本目录包含现代C++编程的核心概念和最佳实践示例。

## 文件说明

### memory_management.cpp

内存管理最佳实践，包括：

- 智能指针（unique_ptr, shared_ptr, weak_ptr）
- RAII模式
- 自定义删除器
- 内存池实现

### concurrent_patterns.cpp

并发编程模式，包括：

- 线程池实现
- 生产者-消费者模式
- 读写锁模式
- Future/Promise模式

### type_traits.cpp

类型特征和元编程，包括：

- 类型萃取（Type Traits）
- SFINAE技巧
- 概念约束（Concepts）
- 编译期计算

## 编译要求

- C++17或更高版本（推荐C++20）
- 支持线程的编译器

## 编译运行

```bash
# 使用g++
g++ -std=c++20 -pthread -o example memory_management.cpp
./example

# 使用clang++
clang++ -std=c++20 -pthread -o example concurrent_patterns.cpp
./example

# 使用MSVC
cl /std:c++20 /EHsc type_traits.cpp
```

## 学习建议

1. 按顺序阅读文件，从内存管理基础开始
2. 尝试修改代码，观察不同实现的效果
3. 关注现代C++的安全性和性能权衡
