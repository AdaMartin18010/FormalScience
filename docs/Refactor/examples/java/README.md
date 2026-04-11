# Java 代码示例

本目录包含现代Java编程的核心概念和最佳实践示例。

## 文件说明

### functional_patterns.java

函数式编程模式，包括：

- Lambda表达式和函数式接口
- Stream API使用
- Optional处理
- 方法引用

### concurrent_collections.java

并发集合，包括：

- ConcurrentHashMap
- CopyOnWriteArrayList
- BlockingQueue
- ConcurrentSkipListMap

### type_system.java

类型系统高级特性，包括：

- 泛型通配符
- 类型边界
- 类型擦除
- 可变参数和类型安全

## 运行要求

- Java 11或更高版本（推荐Java 17+）
- 支持Lambda和Stream API

## 编译运行

```bash
# 编译
javac functional_patterns.java
javac concurrent_collections.java
javac type_system.java

# 运行
java FunctionalPatterns
java ConcurrentCollections
java TypeSystem
```

## 学习建议

1. 从函数式编程开始，理解Lambda和Stream
2. 掌握并发集合的正确使用场景
3. 深入理解Java泛型系统
