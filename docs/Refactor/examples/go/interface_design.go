package main

import (
	"bytes"
	"fmt"
	"io"
	"os"
)

/**
 * Go 接口设计最佳实践示例
 *
 * 本文件演示Go语言中的接口设计：
 * - 隐式接口
 * - 组合优于继承
 * - 接口隔离
 * - 依赖注入
 */

// ============================================
// 1. 隐式接口
// ============================================

// Writer接口定义写入行为
type Writer interface {
	Write(p []byte) (n int, err error)
}

// Reader接口定义读取行为
type Reader interface {
	Read(p []byte) (n int, err error)
}

// ReadWriter组合接口
type ReadWriter interface {
	Reader
	Writer
}

// StringWriter实现Writer接口（隐式实现）
type StringWriter struct {
	content string
}

func (sw *StringWriter) Write(p []byte) (n int, err error) {
	sw.content += string(p)
	return len(p), nil
}

func (sw *StringWriter) String() string {
	return sw.content
}

// FileWriter实现Writer接口
type FileWriter struct {
	filename string
}

func (fw *FileWriter) Write(p []byte) (n int, err error) {
	file, err := os.OpenFile(fw.filename, os.O_APPEND|os.O_CREATE|os.O_WRONLY, 0644)
	if err != nil {
		return 0, err
	}
	defer file.Close()

	return file.Write(p)
}

// 任何实现了Write方法的类型都可以作为参数
func writeData(w Writer, data []byte) error {
	_, err := w.Write(data)
	return err
}

func demonstrateImplicitInterfaces() {
	fmt.Println("=== 隐式接口 ===")

	// 使用StringWriter
	sw := &StringWriter{}
	writeData(sw, []byte("Hello, "))
	writeData(sw, []byte("World!"))
	fmt.Printf("StringWriter内容: %s\n", sw.String())

	// 使用标准库的bytes.Buffer（也实现了Writer）
	var buf bytes.Buffer
	writeData(&buf, []byte("使用bytes.Buffer"))
	fmt.Printf("Buffer内容: %s\n", buf.String())
}

// ============================================
// 2. 组合优于继承
// ============================================

// Logger接口
type Logger interface {
	Log(message string)
}

// ConsoleLogger基础实现
type ConsoleLogger struct {
	prefix string
}

func (cl *ConsoleLogger) Log(message string) {
	fmt.Printf("[%s] %s\n", cl.prefix, message)
}

// TimestampLogger添加时间戳（装饰器模式）
type TimestampLogger struct {
	logger Logger
}

func (tl *TimestampLogger) Log(message string) {
	timestamp := "2024-01-01 12:00:00" // 简化示例
	tl.logger.Log(fmt.Sprintf("[%s] %s", timestamp, message))
}

// LevelLogger添加日志级别
type LevelLogger struct {
	logger Logger
	level  string
}

func (ll *LevelLogger) Log(message string) {
	ll.logger.Log(fmt.Sprintf("[%s] %s", ll.level, message))
}

// 组合多种功能
type CompositeLogger struct {
	*ConsoleLogger
	*TimestampLogger
	*LevelLogger
}

// 实现Log方法（组合所有功能）
func (cl *CompositeLogger) Log(message string) {
	cl.LevelLogger.Log(message)
}

func demonstrateComposition() {
	fmt.Println("\n=== 组合优于继承 ===")

	// 基础logger
	console := &ConsoleLogger{prefix: "APP"}
	console.Log("普通日志")

	// 添加时间戳
	timestamp := &TimestampLogger{logger: console}
	timestamp.Log("带时间戳的日志")

	// 添加日志级别
	level := &LevelLogger{logger: timestamp, level: "INFO"}
	level.Log("带级别和时间戳的日志")
}

// ============================================
// 3. 接口隔离原则
// ============================================

// 不推荐的：大而全的接口
type BigInterface interface {
	Connect()
	Disconnect()
	Read() ([]byte, error)
	Write([]byte) error
	Execute(string) error
}

// 推荐的：细粒度接口

type Connector interface {
	Connect() error
	Disconnect() error
}

type DataReader interface {
	Read() ([]byte, error)
}

type DataWriter interface {
	Write([]byte) error
}

type Executor interface {
	Execute(command string) (string, error)
}

// DatabaseClient只实现它需要的接口
type DatabaseClient struct {
	connected bool
}

func (dc *DatabaseClient) Connect() error {
	dc.connected = true
	return nil
}

func (dc *DatabaseClient) Disconnect() error {
	dc.connected = false
	return nil
}

func (dc *DatabaseClient) Execute(command string) (string, error) {
	if !dc.connected {
		return "", fmt.Errorf("未连接")
	}
	return fmt.Sprintf("执行: %s", command), nil
}

// FileClient实现不同的接口组合
type FileClient struct {
	filename string
	file     *os.File
}

func (fc *FileClient) Connect() error {
	file, err := os.Open(fc.filename)
	if err != nil {
		return err
	}
	fc.file = file
	return nil
}

func (fc *FileClient) Disconnect() error {
	if fc.file != nil {
		return fc.file.Close()
	}
	return nil
}

func (fc *FileClient) Read() ([]byte, error) {
	if fc.file == nil {
		return nil, fmt.Errorf("未连接")
	}
	return io.ReadAll(fc.file)
}

// 使用接口隔离的好处：函数只需要它需要的接口
func processData(reader DataReader) ([]byte, error) {
	return reader.Read()
}

func sendData(writer DataWriter, data []byte) error {
	_, err := writer.Write(data)
	return err
}

func runCommand(executor Executor, cmd string) (string, error) {
	return executor.Execute(cmd)
}

func demonstrateInterfaceSegregation() {
	fmt.Println("\n=== 接口隔离原则 ===")

	// DatabaseClient实现了Connector和Executor
	db := &DatabaseClient{}
	db.Connect()

	result, err := runCommand(db, "SELECT * FROM users")
	if err != nil {
		fmt.Printf("错误: %v\n", err)
	} else {
		fmt.Printf("结果: %s\n", result)
	}

	db.Disconnect()

	// FileClient实现了Connector和DataReader
	fc := &FileClient{filename: "test.txt"}
	// 创建一个测试文件
	os.WriteFile("test.txt", []byte("测试数据"), 0644)

	fc.Connect()
	data, err := processData(fc)
	if err != nil {
		fmt.Printf("错误: %v\n", err)
	} else {
		fmt.Printf("文件内容: %s\n", string(data))
	}
	fc.Disconnect()

	os.Remove("test.txt")
}

// ============================================
// 4. 依赖注入
// ============================================

// Service接口
type Service interface {
	DoWork() string
}

// RealService实际实现
type RealService struct{}

func (rs *RealService) DoWork() string {
	return "Real work done"
}

// MockService测试用实现
type MockService struct {
	ReturnValue string
}

func (ms *MockService) DoWork() string {
	return ms.ReturnValue
}

// Processor依赖Service
type Processor struct {
	service Service
}

// 构造函数注入
func NewProcessor(service Service) *Processor {
	return &Processor{service: service}
}

// Setter注入
func (p *Processor) SetService(service Service) {
	p.service = service
}

func (p *Processor) Process() string {
	return p.service.DoWork()
}

// 接口作为依赖的示例：数据存储
type Storage interface {
	Save(key string, value []byte) error
	Load(key string) ([]byte, error)
}

// MemoryStorage内存存储（测试用）
type MemoryStorage struct {
	data map[string][]byte
}

func NewMemoryStorage() *MemoryStorage {
	return &MemoryStorage{data: make(map[string][]byte)}
}

func (ms *MemoryStorage) Save(key string, value []byte) error {
	ms.data[key] = value
	return nil
}

func (ms *MemoryStorage) Load(key string) ([]byte, error) {
	value, ok := ms.data[key]
	if !ok {
		return nil, fmt.Errorf("key not found: %s", key)
	}
	return value, nil
}

// DataRepository依赖Storage
type DataRepository struct {
	storage Storage
}

func NewDataRepository(storage Storage) *DataRepository {
	return &DataRepository{storage: storage}
}

func (dr *DataRepository) StoreUser(id string, name string) error {
	return dr.storage.Save(fmt.Sprintf("user:%s", id), []byte(name))
}

func (dr *DataRepository) GetUser(id string) (string, error) {
	data, err := dr.storage.Load(fmt.Sprintf("user:%s", id))
	if err != nil {
		return "", err
	}
	return string(data), nil
}

func demonstrateDependencyInjection() {
	fmt.Println("\n=== 依赖注入 ===")

	// 使用真实服务
	realProcessor := NewProcessor(&RealService{})
	fmt.Printf("真实服务: %s\n", realProcessor.Process())

	// 使用Mock服务（测试场景）
	mockProcessor := NewProcessor(&MockService{ReturnValue: "Mock work done"})
	fmt.Printf("Mock服务: %s\n", mockProcessor.Process())

	// 使用内存存储的Repository
	storage := NewMemoryStorage()
	repo := NewDataRepository(storage)

	repo.StoreUser("1", "Alice")
	name, err := repo.GetUser("1")
	if err != nil {
		fmt.Printf("错误: %v\n", err)
	} else {
		fmt.Printf("用户: %s\n", name)
	}
}

// ============================================
// 5. 错误处理接口
// ============================================

// Error接口已经内置在Go中
type error interface {
	Error() string
}

// 自定义错误类型
type NotFoundError struct {
	Resource string
	ID       string
}

func (e *NotFoundError) Error() string {
	return fmt.Sprintf("%s with id '%s' not found", e.Resource, e.ID)
}

// 实现Unwrap接口（Go 1.13+错误链）
func (e *NotFoundError) Unwrap() error {
	return nil // 作为链的末端
}

type ValidationError struct {
	Field   string
	Message string
}

func (e *ValidationError) Error() string {
	return fmt.Sprintf("validation error for field '%s': %s", e.Field, e.Message)
}

// 错误包装
type WrappedError struct {
	Op   string // 操作
	Err  error  // 底层错误
}

func (e *WrappedError) Error() string {
	return fmt.Sprintf("%s: %v", e.Op, e.Err)
}

func (e *WrappedError) Unwrap() error {
	return e.Err
}

// 错误检查辅助函数
func IsNotFound(err error) bool {
	var notFound *NotFoundError
	return fmt.AsError(err, &notFound)
}

func IsValidationError(err error) bool {
	var validation *ValidationError
	return fmt.AsError(err, &validation)
}

// 正确的错误检查方式（Go 1.13+）
func checkError(err error) {
	if err == nil {
		return
	}

	var notFound *NotFoundError
	if fmt.AsError(err, &notFound) {
		fmt.Printf("未找到: %s\n", notFound.Resource)
		return
	}

	var validation *ValidationError
	if fmt.AsError(err, &validation) {
		fmt.Printf("验证失败: %s - %s\n", validation.Field, validation.Message)
		return
	}

	fmt.Printf("其他错误: %v\n", err)
}

func demonstrateErrorHandling() {
	fmt.Println("\n=== 错误处理 ===")

	// 创建不同类型的错误
	err1 := &NotFoundError{Resource: "User", ID: "123"}
	err2 := &ValidationError{Field: "email", Message: "invalid format"}
	wrapped := &WrappedError{Op: "database query", Err: err1}

	fmt.Printf("错误1: %v\n", err1)
	fmt.Printf("错误2: %v\n", err2)
	fmt.Printf("包装错误: %v\n", wrapped)

	// 错误检查
	checkError(err1)
	checkError(err2)
	checkError(wrapped)

	// 使用errors.Is和errors.As（需要标准库errors包）
	// 这里使用fmt.AsError作为简化示例
}

// ============================================
// 6. 空接口和类型断言
// ============================================

// 使用空接口实现泛型容器（Go 1.18之前的方式）
type Container struct {
	items []interface{}
}

func (c *Container) Add(item interface{}) {
	c.items = append(c.items, item)
}

func (c *Container) Get(index int) (interface{}, bool) {
	if index < 0 || index >= len(c.items) {
		return nil, false
	}
	return c.items[index], true
}

// 类型断言使用
func processValue(value interface{}) {
	switch v := value.(type) {
	case int:
		fmt.Printf("整数: %d\n", v)
	case string:
		fmt.Printf("字符串: %s\n", v)
	case bool:
		fmt.Printf("布尔: %t\n", v)
	case []interface{}:
		fmt.Printf("切片，长度: %d\n", len(v))
	default:
		fmt.Printf("未知类型: %T\n", v)
	}
}

// 类型开关
func describeValue(value interface{}) string {
	switch v := value.(type) {
	case fmt.Stringer:
		return v.String()
	case error:
		return v.Error()
	default:
		return fmt.Sprintf("%v", v)
	}
}

// 泛型版本（Go 1.18+）
type GenericContainer[T any] struct {
	items []T
}

func (c *GenericContainer[T]) Add(item T) {
	c.items = append(c.items, item)
}

func (c *GenericContainer[T]) Get(index int) (T, bool) {
	var zero T
	if index < 0 || index >= len(c.items) {
		return zero, false
	}
	return c.items[index], true
}

func demonstrateEmptyInterface() {
	fmt.Println("\n=== 空接口和类型断言 ===")

	// 使用空接口容器
	container := &Container{}
	container.Add(42)
	container.Add("hello")
	container.Add(true)
	container.Add([]interface{}{1, 2, 3})

	for i := 0; i < 4; i++ {
		if item, ok := container.Get(i); ok {
			processValue(item)
		}
	}

	// 使用泛型容器（类型安全）
	fmt.Println("\n--- 泛型容器 ---")
	intContainer := &GenericContainer[int]{}
	intContainer.Add(1)
	intContainer.Add(2)
	intContainer.Add(3)

	if val, ok := intContainer.Get(1); ok {
		fmt.Printf("获取值: %d (类型安全，无需断言)\n", val)
	}
}

// ============================================
// 主函数
// ============================================

func main() {
	fmt.Println("========================================")
	fmt.Println("Go 接口设计最佳实践示例")
	fmt.Println("========================================")

	demonstrateImplicitInterfaces()
	demonstrateComposition()
	demonstrateInterfaceSegregation()
	demonstrateDependencyInjection()
	demonstrateErrorHandling()
	demonstrateEmptyInterface()

	fmt.Println("\n========================================")
	fmt.Println("所有接口设计演示完成")
	fmt.Println("========================================")
}
