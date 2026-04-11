package main

import (
	"context"
	"fmt"
	"math/rand"
	"sync"
	"time"
)

/**
 * Go Channel高级模式示例
 *
 * 本文件演示Go语言中的Channel模式：
 * - Select多路复用
 * - 超时和取消
 * - Fan-Out/Fan-In
 * - 速率限制
 */

// ============================================
// 1. Select多路复用
// ============================================

// 基础Select演示
func demonstrateBasicSelect() {
	fmt.Println("=== Select基础 ===")

	ch1 := make(chan string)
	ch2 := make(chan string)

	// 启动两个goroutine
	go func() {
		time.Sleep(100 * time.Millisecond)
		ch1 <- "来自ch1的消息"
	}()

	go func() {
		time.Sleep(200 * time.Millisecond)
		ch2 <- "来自ch2的消息"
	}()

	// 使用select接收
	for i := 0; i < 2; i++ {
		select {
		case msg1 := <-ch1:
			fmt.Println(msg1)
		case msg2 := <-ch2:
			fmt.Println(msg2)
		}
	}
}

// 非阻塞Select
func demonstrateNonBlockingSelect() {
	fmt.Println("\n=== 非阻塞Select ===")

	ch := make(chan string)

	// 非阻塞发送
	select {
	case ch <- "尝试发送":
		fmt.Println("发送成功")
	default:
		fmt.Println("发送失败（Channel已满或未准备好）")
	}

	// 非阻塞接收
	select {
	case msg := <-ch:
		fmt.Println("接收到:", msg)
	default:
		fmt.Println("没有可用消息")
	}

	// 带缓冲的Channel
	buffered := make(chan int, 2)
	buffered <- 1
	buffered <- 2

	// 非阻塞检查多个channel
	for {
		select {
		case v := <-buffered:
			fmt.Printf("接收到: %d\n", v)
		default:
			fmt.Println("Channel已空")
			return
		}
	}
}

// 随机Select
func demonstrateRandomSelect() {
	fmt.Println("\n=== 随机Select ===")

	ch1 := make(chan int, 10)
	ch2 := make(chan int, 10)

	// 填充数据
	for i := 0; i < 5; i++ {
		ch1 <- i
		ch2 <- i + 100
	}

	// 随机选择可用的case
	for i := 0; i < 10; i++ {
		select {
		case v := <-ch1:
			fmt.Printf("从ch1接收: %d\n", v)
		case v := <-ch2:
			fmt.Printf("从ch2接收: %d\n", v)
		}
	}
}

// ============================================
// 2. 超时和取消模式
// ============================================

// 超时模式
func operationWithTimeout() {
	fmt.Println("\n=== 超时模式 ===")

	// 模拟慢操作
	slowOperation := func() <-chan string {
		result := make(chan string)
		go func() {
			time.Sleep(2 * time.Second)
			result <- "操作完成"
		}()
		return result
	}

	select {
	case result := <-slowOperation():
		fmt.Println(result)
	case <-time.After(1 * time.Second):
		fmt.Println("操作超时")
	}
}

// 使用Context取消
func demonstrateContextCancellation() {
	fmt.Println("\n=== Context取消模式 ===")

	ctx, cancel := context.WithCancel(context.Background())

	// 启动工作goroutine
	go func(ctx context.Context) {
		for {
			select {
			case <-ctx.Done():
				fmt.Println("Worker: 收到取消信号")
				return
			default:
				fmt.Println("Worker: 工作中...")
				time.Sleep(200 * time.Millisecond)
			}
		}
	}(ctx)

	time.Sleep(500 * time.Millisecond)
	fmt.Println("主程序：发送取消信号")
	cancel()

	time.Sleep(300 * time.Millisecond)
}

// 优雅关闭Channel
func demonstrateGracefulShutdown() {
	fmt.Println("\n=== 优雅关闭 ===")

	jobs := make(chan int, 10)
	done := make(chan struct{})
	var wg sync.WaitGroup

	// 启动worker
	for i := 0; i < 3; i++ {
		wg.Add(1)
		go func(id int) {
			defer wg.Done()
			for job := range jobs {
				fmt.Printf("Worker %d 处理 job %d\n", id, job)
				time.Sleep(100 * time.Millisecond)
			}
			fmt.Printf("Worker %d 退出\n", id)
		}(i)
	}

	// 发送任务
	go func() {
		for i := 1; i <= 10; i++ {
			jobs <- i
		}
		close(jobs)
	}()

	// 等待所有worker完成
	go func() {
		wg.Wait()
		close(done)
	}()

	// 使用select等待完成或超时
	select {
	case <-done:
		fmt.Println("所有worker正常退出")
	case <-time.After(3 * time.Second):
		fmt.Println("等待超时")
	}
}

// ============================================
// 3. Fan-Out/Fan-In模式
// ============================================

// 生成数字序列
func generate(nums ...int) <-chan int {
	out := make(chan int)
	go func() {
		for _, n := range nums {
			out <- n
		}
		close(out)
	}()
	return out
}

// 平方计算
func square(in <-chan int) <-chan int {
	out := make(chan int)
	go func() {
		for n := range in {
			out <- n * n
		}
		close(out)
	}()
	return out
}

// Fan-Out：多个worker处理同一输入
func fanOut(in <-chan int, numWorkers int) []<-chan int {
	var workers []<-chan int
	for i := 0; i < numWorkers; i++ {
		workers = append(workers, square(in))
	}
	return workers
}

// Fan-In：合并多个channel
func fanIn(channels ...<-chan int) <-chan int {
	var wg sync.WaitGroup
	out := make(chan int)

	output := func(c <-chan int) {
		defer wg.Done()
		for n := range c {
			out <- n
		}
	}

	wg.Add(len(channels))
	for _, c := range channels {
		go output(c)
	}

	go func() {
		wg.Wait()
		close(out)
	}()

	return out
}

func demonstrateFanOutFanIn() {
	fmt.Println("\n=== Fan-Out/Fan-In模式 ===")

	// 生成输入
	in := generate(1, 2, 3, 4, 5, 6, 7, 8, 9, 10)

	// Fan-Out：3个worker并行处理
	workers := fanOut(in, 3)

	// Fan-In：合并结果
	results := fanIn(workers...)

	// 收集结果
	var sum int
	for result := range results {
		fmt.Printf("%d ", result)
		sum += result
	}
	fmt.Printf("\n总和: %d\n", sum)
}

// 带停止信号的Fan-Out/Fan-In
func fanOutWithDone(in <-chan int, done <-chan struct{}, numWorkers int) []<-chan int {
	var workers []<-chan int
	for i := 0; i < numWorkers; i++ {
		out := make(chan int)
		go func() {
			defer close(out)
			for {
				select {
				case n, ok := <-in:
					if !ok {
						return
					}
					select {
					case out <- n * n:
					case <-done:
						return
					}
				case <-done:
					return
				}
			}
		}()
		workers = append(workers, out)
	}
	return workers
}

// ============================================
// 4. 速率限制
// ============================================

// 令牌桶限流器
type TokenBucket struct {
	rate       float64    // 每秒产生的令牌数
	capacity   float64    // 桶容量
	tokens     float64    // 当前令牌数
	lastUpdate time.Time  // 上次更新时间
	mutex      sync.Mutex
}

func NewTokenBucket(rate, capacity float64) *TokenBucket {
	return &TokenBucket{
		rate:       rate,
		capacity:   capacity,
		tokens:     capacity,
		lastUpdate: time.Now(),
	}
}

func (tb *TokenBucket) Allow() bool {
	tb.mutex.Lock()
	defer tb.mutex.Unlock()

	now := time.Now()
	elapsed := now.Sub(tb.lastUpdate).Seconds()
	tb.lastUpdate = now

	// 添加新令牌
	tb.tokens += elapsed * tb.rate
	if tb.tokens > tb.capacity {
		tb.tokens = tb.capacity
	}

	// 尝试获取令牌
	if tb.tokens >= 1 {
		tb.tokens--
		return true
	}
	return false
}

func (tb *TokenBucket) Wait() {
	for !tb.Allow() {
		time.Sleep(10 * time.Millisecond)
	}
}

// 使用Channel实现限流
func rateLimitByChannel() {
	fmt.Println("\n=== Channel限流 ===")

	// 每秒处理3个请求
	limiter := time.Tick(333 * time.Millisecond)

	requests := make(chan int, 10)
	for i := 1; i <= 10; i++ {
		requests <- i
	}
	close(requests)

	for req := range requests {
		<-limiter
		fmt.Printf("处理请求 %d (时间: %s)\n", req, time.Now().Format("15:04:05.000"))
	}
}

// 突发限流
func burstyRateLimit() {
	fmt.Println("\n=== 突发限流 ===")

	// 允许突发3个请求，然后每200ms一个
	burstLimiter := make(chan time.Time, 3)
	for i := 0; i < 3; i++ {
		burstLimiter <- time.Now()
	}

	// 补充令牌
	go func() {
		ticker := time.NewTicker(200 * time.Millisecond)
		for t := range ticker.C {
			select {
			case burstLimiter <- t:
			default:
			}
		}
	}()

	// 模拟突发请求
	requests := []int{1, 2, 3, 4, 5, 6, 7, 8}

	for _, req := range requests {
		<-burstLimiter
		fmt.Printf("处理请求 %d (时间: %s)\n", req, time.Now().Format("15:04:05.000"))
	}
}

// 自适应限流
func demonstrateAdaptiveRateLimit() {
	fmt.Println("\n=== 自适应限流 ===")

	type Task struct {
		ID   int
		Work func() error
	}

	tasks := make(chan Task, 20)
	results := make(chan string, 20)

	// 生产者
	go func() {
		for i := 1; i <= 20; i++ {
			tasks <- Task{
				ID: i,
				Work: func() error {
					// 模拟可能失败的工作
					if rand.Float32() < 0.3 {
						return fmt.Errorf("随机失败")
					}
					time.Sleep(50 * time.Millisecond)
					return nil
				},
			}
		}
		close(tasks)
	}()

	// 消费者（带自适应速率）
	var wg sync.WaitGroup
	worker := func() {
		defer wg.Done()
		consecutiveErrors := 0

		for task := range tasks {
			// 自适应延迟：错误越多，延迟越长
			delay := time.Duration(consecutiveErrors) * 50 * time.Millisecond
			time.Sleep(delay)

			if err := task.Work(); err != nil {
				results <- fmt.Sprintf("Task %d 失败: %v", task.ID, err)
				consecutiveErrors++
				if consecutiveErrors > 5 {
					consecutiveErrors = 5 // 最大延迟限制
				}
			} else {
				results <- fmt.Sprintf("Task %d 成功", task.ID)
				consecutiveErrors = 0
			}
		}
	}

	// 启动多个worker
	for i := 0; i < 3; i++ {
		wg.Add(1)
		go worker()
	}

	// 等待完成
	go func() {
		wg.Wait()
		close(results)
	}()

	// 收集结果
	successCount := 0
	failCount := 0
	for result := range results {
		if successCount+failCount < 5 {
			fmt.Println(result)
		}
		if contains(result, "成功") {
			successCount++
		} else {
			failCount++
		}
	}

	fmt.Printf("... (共 %d 成功, %d 失败)\n", successCount, failCount)
}

func contains(s, substr string) bool {
	return len(s) >= len(substr) && (s == substr || len(s) > 0 && containsHelper(s, substr))
}

func containsHelper(s, substr string) bool {
	for i := 0; i <= len(s)-len(substr); i++ {
		if s[i:i+len(substr)] == substr {
			return true
		}
	}
	return false
}

// ============================================
// 5. Pipeline错误处理
// ============================================

// 带错误的结果
type Result struct {
	Value int
	Error error
}

// 可能失败的stage
func squareWithError(in <-chan int) <-chan Result {
	out := make(chan Result)
	go func() {
		defer close(out)
		for n := range in {
			if n < 0 {
				out <- Result{Error: fmt.Errorf("负数不支持: %d", n)}
			} else {
				out <- Result{Value: n * n}
			}
		}
	}()
	return out
}

// 错误处理pipeline
func demonstrateErrorHandlingPipeline() {
	fmt.Println("\n=== Pipeline错误处理 ===")

	input := make(chan int)
	go func() {
		nums := []int{1, 2, -3, 4, -5, 6}
		for _, n := range nums {
			input <- n
		}
		close(input)
	}()

	results := squareWithError(input)

	for result := range results {
		if result.Error != nil {
			fmt.Printf("错误: %v\n", result.Error)
		} else {
			fmt.Printf("结果: %d\n", result.Value)
		}
	}
}

// ============================================
// 6. 高级Select模式
// ============================================

// 心跳模式
func heartbeat() {
	fmt.Println("\n=== 心跳模式 ===")

	doWork := func(done <-chan struct{}, pulseInterval time.Duration) (<-chan struct{}, <-chan string) {
		heartbeat := make(chan struct{})
		results := make(chan string)

		go func() {
			defer close(heartbeat)
			defer close(results)

			pulse := time.NewTicker(pulseInterval)
			workTicker := time.NewTicker(pulseInterval * 2)

			sendPulse := func() {
				select {
				case heartbeat <- struct{}{}:
				default:
				}
			}

			sendResult := func(r string) {
				for {
					select {
					case <-done:
						return
					case <-pulse.C:
						sendPulse()
					case results <- r:
						return
					}
				}
			}

			for {
				select {
				case <-done:
					return
				case <-pulse.C:
					sendPulse()
				case <-workTicker.C:
					sendResult("工作结果")
				}
			}
		}()

		return heartbeat, results
	}

	done := make(chan struct{})
	heartbeat, results := doWork(done, 200*time.Millisecond)

	// 监听10个心跳
	for i := 0; i < 10; i++ {
		select {
		case <-heartbeat:
			fmt.Printf("[%d] 心跳\n", i+1)
		case r := <-results:
			fmt.Printf("[%d] 结果: %s\n", i+1, r)
		}
	}

	close(done)
}

//  or-done-channel模式
func or(channels ...<-chan struct{}) <-chan struct{} {
	switch len(channels) {
	case 0:
		return nil
	case 1:
		return channels[0]
	}

	orDone := make(chan struct{})
	go func() {
		defer close(orDone)

		switch len(channels) {
		case 2:
			select {
			case <-channels[0]:
			case <-channels[1]:
			}
		default:
			select {
			case <-channels[0]:
			case <-channels[1]:
			case <-channels[2]:
			case <-or(append(channels[3:], orDone)...):
			}
		}
	}()

	return orDone
}

// tee-channel模式：一个输入，多个输出
func tee(in <-chan int, outs ...chan<- int) {
	go func() {
		defer func() {
			for _, out := range outs {
				close(out)
			}
		}()

		for val := range in {
			for _, out := range outs {
				out <- val
			}
		}
	}()
}

func demonstrateAdvancedSelect() {
	fmt.Println("\n=== 高级Select模式 ===")

	// Tee模式演示
	in := make(chan int)
	out1, out2 := make(chan int), make(chan int)

	tee(in, out1, out2)

	// 发送数据
	go func() {
		for i := 1; i <= 3; i++ {
			in <- i
		}
		close(in)
	}()

	// 接收数据
	var wg sync.WaitGroup
	wg.Add(2)

	go func() {
		defer wg.Done()
		for v := range out1 {
			fmt.Printf("Out1 收到: %d\n", v)
		}
	}()

	go func() {
		defer wg.Done()
		for v := range out2 {
			fmt.Printf("Out2 收到: %d\n", v)
		}
	}()

	wg.Wait()
}

// ============================================
// 主函数
// ============================================

func main() {
	rand.Seed(time.Now().UnixNano())

	fmt.Println("========================================")
	fmt.Println("Go Channel高级模式示例")
	fmt.Println("========================================")

	demonstrateBasicSelect()
	demonstrateNonBlockingSelect()
	demonstrateRandomSelect()
	operationWithTimeout()
	demonstrateContextCancellation()
	demonstrateGracefulShutdown()
	demonstrateFanOutFanIn()
	rateLimitByChannel()
	burstyRateLimit()
	demonstrateAdaptiveRateLimit()
	demonstrateErrorHandlingPipeline()
	heartbeat()
	demonstrateAdvancedSelect()

	fmt.Println("\n========================================")
	fmt.Println("所有Channel模式演示完成")
	fmt.Println("========================================")
}
