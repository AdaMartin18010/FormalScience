# Go 代码示例

本目录包含现代Go编程的核心概念和最佳实践示例。

## 文件说明

### concurrent_patterns.go

并发编程模式，包括：

- Goroutine和Channel基础
- Worker Pool模式
- Pipeline模式
- Context取消

### interface_design.go

接口设计最佳实践，包括：

- 隐式接口
- 组合优于继承
- 接口隔离
- 依赖注入

### channel_patterns.go

Channel高级模式，包括：

- Select多路复用
- 超时和取消
- Fan-Out/Fan-In
- 速率限制

## 运行要求

- Go 1.18或更高版本（推荐1.21+）
- 支持泛型

## 编译运行

```bash
# 运行单个文件
go run concurrent_patterns.go
go run interface_design.go
go run channel_patterns.go

# 编译
go build concurrent_patterns.go
go build interface_design.go
go build channel_patterns.go
```

## 学习建议

1. 先理解Go的并发哲学：不要通过共享内存通信，而是通过通信共享内存
2. 掌握接口的隐式实现机制
3. 熟练使用Channel进行协调
