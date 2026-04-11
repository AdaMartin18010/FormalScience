package main

import (
	"context"
	"fmt"
	"math/rand"
	"sync"
	"time"
)

/**
 * Go 并发编程模式示例
 *
 * 本文件演示Go语言中的并发模式：
 * - Goroutine和Channel基础
 * - Worker Pool模式
 * - Pipeline模式
 * - Context取消
 */

// ============================================
// 1. Goroutine和Channel基础
// ============================================

// 基础Goroutine演示
func demonstrateBasicGoroutines() {
	fmt.Println("=== Goroutine和Channel基础 ===")

	// 使用WaitGroup等待goroutine完成
	var wg sync.WaitGroup

	for i := 1; i <= 3; i++ {
		wg.Add(1)
		go func(id int) {
			defer wg.Done()
			fmt.Printf("Goroutine %d 开始\n", id)
			time.Sleep(time.Duration(rand.Intn(500)) * time.Millisecond)
			fmt.Printf("Goroutine %d 完成\n", id)
		}(i)
	}

	wg.Wait()
	fmt.Println("所有Goroutine完成")
}

// Channel基础演示
func demonstrateChannels() {
	fmt.Println("\n=== Channel基础 ===")

	// 无缓冲Channel（同步通信）
	unbuffered := make(chan int)
	go func() {
		fmt.Println("发送者：准备发送")
		unbuffered <- 42
		fmt.Println("发送者：发送完成")
	}()

	fmt.Println("主程序：准备接收")
	value := <-unbuffered
	fmt.Printf("主程序：接收 %d\n", value)

	// 有缓冲Channel（异步通信）
	buffered := make(chan string, 3)
	buffered <- "第一"
	buffered <- "第二"
	buffered <- "第三"
	fmt.Printf("Channel中有 %d 个元素\n", len(buffered))

	close(buffered)

	// 遍历关闭的Channel
	for msg := range buffered {
		fmt.Printf("接收: %s\n", msg)
	}
}

// 方向性Channel
func demonstrateDirectionalChannels() {
	fmt.Println("\n=== 方向性Channel ===")

	// 只能发送
	sender := func(ch chan<- int) {
		for i := 0; i < 3; i++ {
			ch <- i
			fmt.Printf("发送: %d\n", i)
		}
		close(ch)
	}

	// 只能接收
	receiver := func(ch <-chan int) {
		for value := range ch {
			fmt.Printf("接收: %d\n", value)
		}
	}

	ch := make(chan int, 3)
	go sender(ch)
	receiver(ch)
}

// ============================================
// 2. Worker Pool模式
// ============================================

// Job表示一个工作任务
type Job struct {
	ID   int
	Data string
}

// Result表示工作结果
type Result struct {
	Job    Job
	Output string
	Error  error
}

// Worker表示一个工作goroutine
func worker(id int, jobs <-chan Job, results chan<- Result, wg *sync.WaitGroup) {
	defer wg.Done()
	for job := range jobs {
		fmt.Printf("Worker %d 处理 Job %d\n", id, job.ID)

		// 模拟工作
		time.Sleep(time.Duration(rand.Intn(500)) * time.Millisecond)

		results <- Result{
			Job:    job,
			Output: fmt.Sprintf("Result of %s", job.Data),
		}
	}
}

// WorkerPool实现任务并发处理
func workerPool(numWorkers int, jobs []Job) []Result {
	jobChan := make(chan Job, len(jobs))
	resultChan := make(chan Result, len(jobs))

	var wg sync.WaitGroup

	// 启动workers
	for i := 0; i < numWorkers; i++ {
		wg.Add(1)
		go worker(i, jobChan, resultChan, &wg)
	}

	// 发送任务
	go func() {
		for _, job := range jobs {
			jobChan <- job
		}
		close(jobChan)
	}()

	// 等待所有worker完成并关闭结果channel
	go func() {
		wg.Wait()
		close(resultChan)
	}()

	// 收集结果
	var results []Result
	for result := range resultChan {
		results = append(results, result)
	}

	return results
}

func demonstrateWorkerPool() {
	fmt.Println("\n=== Worker Pool模式 ===")

	// 创建10个任务
	var jobs []Job
	for i := 1; i <= 10; i++ {
		jobs = append(jobs, Job{ID: i, Data: fmt.Sprintf("Task-%d", i)})
	}

	results := workerPool(3, jobs)

	fmt.Printf("\n完成 %d 个任务\n", len(results))
	for _, r := range results {
		fmt.Printf("  Job %d: %s\n", r.Job.ID, r.Output)
	}
}

// ============================================
// 3. Pipeline模式
// ============================================

// PipelineStage表示一个处理阶段
type PipelineStage func(in <-chan int) <-chan int

// Generator生成数字序列
func generator(nums ...int) <-chan int {
	out := make(chan int)
	go func() {
		for _, n := range nums {
			out <- n
		}
		close(out)
	}()
	return out
}

// Square将数字平方
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

// Filter过滤奇数
func filterOdd(in <-chan int) <-chan int {
	out := make(chan int)
	go func() {
		for n := range in {
			if n%2 == 0 {
				out <- n
			}
		}
		close(out)
	}()
	return out
}

// 合并多个channel（Fan-In）
func merge(channels ...<-chan int) <-chan int {
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

func demonstratePipeline() {
	fmt.Println("\n=== Pipeline模式 ===")

	// 构建pipeline: generator -> square -> filterOdd
	nums := generator(1, 2, 3, 4, 5, 6, 7, 8, 9, 10)
	squared := square(nums)
	evens := filterOdd(squared)

	fmt.Println("平方后的偶数:")
	for n := range evens {
		fmt.Printf("  %d ", n)
	}
	fmt.Println()

	// 多个Pipeline并行（Fan-Out/Fan-In）
	fmt.Println("\n并行Pipeline:")
	nums2 := generator(1, 2, 3, 4, 5, 6, 7, 8, 9, 10)

	// Fan-Out：两个goroutine处理相同输入
	c1 := square(nums2)
	c2 := square(nums2)

	// Fan-In：合并结果
	merged := merge(c1, c2)

	count := 0
	for range merged {
		count++
	}
	fmt.Printf("合并后共有 %d 个结果\n", count)
}

// ============================================
// 4. Context取消
// ============================================

// 可取消的工作
func cancellableWork(ctx context.Context, id int) {
	for {
		select {
		case <-ctx.Done():
			fmt.Printf("Worker %d: 被取消 - %v\n", id, ctx.Err())
			return
		default:
			fmt.Printf("Worker %d: 工作中...\n", id)
			time.Sleep(200 * time.Millisecond)
		}
	}
}

// 带超时的操作
func operationWithTimeout() {
	fmt.Println("\n=== 超时操作 ===")

	ctx, cancel := context.WithTimeout(context.Background(), 1*time.Second)
	defer cancel()

	select {
	case <-time.After(2 * time.Second):
		fmt.Println("操作完成")
	case <-ctx.Done():
		fmt.Printf("操作超时: %v\n", ctx.Err())
	}
}

// 级联取消
cascadingCancellation() {
	fmt.Println("\n=== 级联取消 ===")

	parentCtx, parentCancel := context.WithCancel(context.Background())
	defer parentCancel()

	// 启动多个worker
	for i := 1; i <= 3; i++ {
		go cancellableWork(parentCtx, i)
	}

	// 让它们运行一会儿
	time.Sleep(500 * time.Millisecond)

	// 取消父context，所有子goroutine都会收到取消信号
	fmt.Println("发送取消信号...")
	parentCancel()

	time.Sleep(200 * time.Millisecond)
}

// 带值的Context
func demonstrateContextWithValue() {
	fmt.Println("\n=== Context带值 ===")

	type contextKey string

	key := contextKey("requestID")
	ctx := context.WithValue(context.Background(), key, "req-12345")

	processRequest := func(ctx context.Context) {
		if requestID, ok := ctx.Value(key).(string); ok {
			fmt.Printf("处理请求: %s\n", requestID)
		}
	}

	processRequest(ctx)
}

// ============================================
// 5. 并发安全的数据结构
// ============================================

// 线程安全的计数器
type SafeCounter struct {
	mu    sync.Mutex
	value int
}

func (c *SafeCounter) Increment() {
	c.mu.Lock()
	defer c.mu.Unlock()
	c.value++
}

func (c *SafeCounter) Value() int {
	c.mu.Lock()
	defer c.mu.Unlock()
	return c.value
}

// 使用原子操作的计数器（更高效）
type AtomicCounter struct {
	value int64
}

// 使用RWMutex的缓存
type SafeCache struct {
	mu    sync.RWMutex
	items map[string]interface{}
}

func NewSafeCache() *SafeCache {
	return &SafeCache{items: make(map[string]interface{})}
}

func (c *SafeCache) Set(key string, value interface{}) {
	c.mu.Lock()
	defer c.mu.Unlock()
	c.items[key] = value
}

func (c *SafeCache) Get(key string) (interface{}, bool) {
	c.mu.RLock()
	defer c.mu.RUnlock()
	val, ok := c.items[key]
	return val, ok
}

func demonstrateConcurrencySafeStructures() {
	fmt.Println("\n=== 并发安全的数据结构 ===")

	// SafeCounter演示
	counter := &SafeCounter{}
	var wg sync.WaitGroup

	for i := 0; i < 100; i++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			for j := 0; j < 100; j++ {
				counter.Increment()
			}
		}()
	}

	wg.Wait()
	fmt.Printf("SafeCounter最终值: %d (期望: 10000)\n", counter.Value())

	// SafeCache演示
	cache := NewSafeCache()

	// 并发写入
	for i := 0; i < 10; i++ {
		wg.Add(1)
		go func(n int) {
			defer wg.Done()
			cache.Set(fmt.Sprintf("key%d", n), n)
		}(i)
	}

	// 并发读取
	for i := 0; i < 10; i++ {
		wg.Add(1)
		go func(n int) {
			defer wg.Done()
			if val, ok := cache.Get(fmt.Sprintf("key%d", n)); ok {
				fmt.Printf("读取 key%d = %v\n", n, val)
			}
		}(i)
	}

	wg.Wait()
}

// ============================================
// 6. 并发模式总结
// ============================================

// Once模式：确保只执行一次
func demonstrateOnce() {
	fmt.Println("\n=== Once模式 ===")

	var once sync.Once
	var wg sync.WaitGroup

	for i := 0; i < 10; i++ {
		wg.Add(1)
		go func(id int) {
			defer wg.Done()
			once.Do(func() {
				fmt.Printf("初始化（由goroutine %d 执行）\n", id)
			})
			fmt.Printf("Goroutine %d 执行完毕\n", id)
		}(i)
	}

	wg.Wait()
}

// Pool模式：对象复用
func demonstratePool() {
	fmt.Println("\n=== Pool模式 ===")

	var pool = sync.Pool{
		New: func() interface{} {
			fmt.Println("创建新对象")
			return make([]byte, 1024)
		},
	}

	// 获取对象
	obj1 := pool.Get()
	fmt.Printf("获取对象: %T\n", obj1)

	// 归还对象
	pool.Put(obj1)

	// 再次获取（可能是同一个对象）
	obj2 := pool.Get()
	fmt.Printf("再次获取对象: %T\n", obj2)

	pool.Put(obj2)
}

// ============================================
// 主函数
// ============================================

func main() {
	rand.Seed(time.Now().UnixNano())

	fmt.Println("========================================")
	fmt.Println("Go 并发编程模式示例")
	fmt.Println("========================================")

	demonstrateBasicGoroutines()
	demonstrateChannels()
	demonstrateDirectionalChannels()
	demonstrateWorkerPool()
	demonstratePipeline()
	operationWithTimeout()
	cascadingCancellation()
	demonstrateContextWithValue()
	demonstrateConcurrencySafeStructures()
	demonstrateOnce()
	demonstratePool()

	fmt.Println("\n========================================")
	fmt.Println("所有并发模式演示完成")
	fmt.Println("========================================")
}
