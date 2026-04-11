# Scala 代码示例

本目录包含现代Scala编程的核心概念和最佳实践示例。

## 文件说明

### functional_programming.scala

函数式编程核心概念，包括：

- 高阶函数
- 不可变数据结构
- 模式匹配
- for推导式

### type_classes.scala

类型类模式，包括：

- 类型类定义
- 隐式实例
- 扩展方法
- 类型类推导

### actor_model.scala

Actor模型编程，包括：

- Actor基础
- 消息传递
- Actor生命周期
- 监督策略

## 运行要求

- Scala 2.13或3.x（推荐3.3+）
- sbt 1.5或更高版本

## 编译运行

```bash
# 使用Scala CLI（推荐）
scala functional_programming.scala
scala type_classes.scala
scala actor_model.scala

# 或使用sbt
sbt run
```

## 学习建议

1. 从函数式编程基础开始，理解Scala的混合范式
2. 掌握类型类，这是Scala的强类型抽象核心
3. 学习Actor模型，理解并发编程的不同范式
