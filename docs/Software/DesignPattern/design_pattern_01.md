# Rust 2024 设计模式实现指南：创建型、结构型与行为型模式

## 一、创建型设计模式在 Rust 2024 中的实现

### 1. 单例模式（Singleton Pattern）

```rust
// 方法一：使用静态变量和懒加载
use std::sync::{Arc, Mutex, Once};
use std::sync::atomic::{AtomicBool, Ordering};
use once_cell::sync::Lazy;

struct Singleton {
    data: String,
}

impl Singleton {
    fn new() -> Self {
        println!("初始化单例");
        Singleton {
            data: "单例数据".to_string(),
        }
    }
    
    fn get_data(&self) -> &str {
        &self.data
    }
}

// 使用once_cell实现线程安全的懒加载单例
static INSTANCE: Lazy<Mutex<Singleton>> = Lazy::new(|| {
    Mutex::new(Singleton::new())
});

// 使用示例
fn singleton_example() {
    // 第一次访问时初始化
    let singleton = INSTANCE.lock().unwrap();
    println!("数据: {}", singleton.get_data());
    
    // 再次访问时使用已有实例
    let singleton2 = INSTANCE.lock().unwrap();
    println!("数据: {}", singleton2.get_data());
}

// 方法二：使用类型系统确保单一实例
struct SingletonToken(());

struct SingletonService {
    data: String,
}

impl SingletonService {
    // 私有构造函数，只能通过get_instance获取
    fn new(_token: SingletonToken) -> Self {
        println!("初始化单例服务");
        SingletonService {
            data: "单例服务数据".to_string(),
        }
    }
    
    // 全局访问点
    fn get_instance() -> &'static SingletonService {
        static INIT: Once = Once::new();
        static mut INSTANCE: Option<SingletonService> = None;
        
        INIT.call_once(|| {
            let token = SingletonToken(());
            let instance = SingletonService::new(token);
            
            unsafe {
                INSTANCE = Some(instance);
            }
        });
        
        unsafe { INSTANCE.as_ref().unwrap() }
    }
    
    fn get_data(&self) -> &str {
        &self.data
    }
}
```

### 2. 工厂方法模式（Factory Method Pattern）

```rust
// 工厂方法模式
trait Product {
    fn operation(&self) -> String;
}

trait Creator {
    // 工厂方法
    fn create_product(&self) -> Box<dyn Product>;
    
    // 使用产品的方法
    fn some_operation(&self) -> String {
        let product = self.create_product();
        format!("创建者: {}", product.operation())
    }
}

// 具体产品
struct ConcreteProductA;
impl Product for ConcreteProductA {
    fn operation(&self) -> String {
        "产品A的结果".to_string()
    }
}

struct ConcreteProductB;
impl Product for ConcreteProductB {
    fn operation(&self) -> String {
        "产品B的结果".to_string()
    }
}

// 具体创建者
struct ConcreteCreatorA;
impl Creator for ConcreteCreatorA {
    fn create_product(&self) -> Box<dyn Product> {
        Box::new(ConcreteProductA)
    }
}

struct ConcreteCreatorB;
impl Creator for ConcreteCreatorB {
    fn create_product(&self) -> Box<dyn Product> {
        Box::new(ConcreteProductB)
    }
}

// 使用示例
fn factory_method_example() {
    let creator_a = ConcreteCreatorA;
    println!("{}", creator_a.some_operation());
    
    let creator_b = ConcreteCreatorB;
    println!("{}", creator_b.some_operation());
}
```

### 3. 抽象工厂模式（Abstract Factory Pattern）

```rust
// 抽象工厂模式
trait Button {
    fn render(&self) -> String;
    fn on_click(&self);
}

trait Checkbox {
    fn render(&self) -> String;
    fn toggle(&mut self);
    fn is_checked(&self) -> bool;
}

// 抽象工厂接口
trait GUIFactory {
    fn create_button(&self) -> Box<dyn Button>;
    fn create_checkbox(&self) -> Box<dyn Checkbox>;
}

// Windows风格具体产品
struct WindowsButton;
impl Button for WindowsButton {
    fn render(&self) -> String {
        "渲染Windows按钮".to_string()
    }
    
    fn on_click(&self) {
        println!("Windows按钮被点击");
    }
}

struct WindowsCheckbox {
    checked: bool,
}

impl Checkbox for WindowsCheckbox {
    fn render(&self) -> String {
        format!("渲染Windows复选框 [{}]", if self.is_checked() { "✓" } else { " " })
    }
    
    fn toggle(&mut self) {
        self.checked = !self.checked;
        println!("Windows复选框状态: {}", if self.checked { "选中" } else { "未选中" });
    }
    
    fn is_checked(&self) -> bool {
        self.checked
    }
}

// MacOS风格具体产品
struct MacOSButton;
impl Button for MacOSButton {
    fn render(&self) -> String {
        "渲染MacOS按钮".to_string()
    }
    
    fn on_click(&self) {
        println!("MacOS按钮被点击");
    }
}

struct MacOSCheckbox {
    checked: bool,
}

impl Checkbox for MacOSCheckbox {
    fn render(&self) -> String {
        format!("渲染MacOS复选框 [{}]", if self.is_checked() { "✓" } else { " " })
    }
    
    fn toggle(&mut self) {
        self.checked = !self.checked;
        println!("MacOS复选框状态: {}", if self.checked { "选中" } else { "未选中" });
    }
    
    fn is_checked(&self) -> bool {
        self.checked
    }
}

// 具体工厂
struct WindowsFactory;
impl GUIFactory for WindowsFactory {
    fn create_button(&self) -> Box<dyn Button> {
        Box::new(WindowsButton)
    }
    
    fn create_checkbox(&self) -> Box<dyn Checkbox> {
        Box::new(WindowsCheckbox { checked: false })
    }
}

struct MacOSFactory;
impl GUIFactory for MacOSFactory {
    fn create_button(&self) -> Box<dyn Button> {
        Box::new(MacOSButton)
    }
    
    fn create_checkbox(&self) -> Box<dyn Checkbox> {
        Box::new(MacOSCheckbox { checked: false })
    }
}

// 客户端代码
struct Application {
    factory: Box<dyn GUIFactory>,
    button: Option<Box<dyn Button>>,
    checkbox: Option<Box<dyn Checkbox>>,
}

impl Application {
    fn new(factory: Box<dyn GUIFactory>) -> Self {
        Application {
            factory,
            button: None,
            checkbox: None,
        }
    }
    
    fn create_ui(&mut self) {
        self.button = Some(self.factory.create_button());
        self.checkbox = Some(self.factory.create_checkbox());
    }
    
    fn render(&self) -> String {
        let button_render = self.button.as_ref().map_or("无按钮".to_string(), |b| b.render());
        let checkbox_render = self.checkbox.as_ref().map_or("无复选框".to_string(), |c| c.render());
        format!("{}\n{}", button_render, checkbox_render)
    }
}

// 使用示例
fn abstract_factory_example() {
    // 创建Windows风格应用
    let windows_factory: Box<dyn GUIFactory> = Box::new(WindowsFactory);
    let mut windows_app = Application::new(windows_factory);
    windows_app.create_ui();
    println!("Windows UI:\n{}", windows_app.render());
    
    // 创建MacOS风格应用
    let macos_factory: Box<dyn GUIFactory> = Box::new(MacOSFactory);
    let mut macos_app = Application::new(macos_factory);
    macos_app.create_ui();
    println!("MacOS UI:\n{}", macos_app.render());
}
```

### 4. 建造者模式（Builder Pattern）

```rust
// 建造者模式
#[derive(Debug, Default)]
struct Computer {
    cpu: String,
    ram: u32,
    storage: u32,
    gpu: Option<String>,
    network_card: Option<String>,
}

struct ComputerBuilder {
    computer: Computer,
}

impl ComputerBuilder {
    fn new() -> Self {
        ComputerBuilder {
            computer: Computer::default(),
        }
    }
    
    fn cpu(mut self, cpu: impl Into<String>) -> Self {
        self.computer.cpu = cpu.into();
        self
    }
    
    fn ram(mut self, ram: u32) -> Self {
        self.computer.ram = ram;
        self
    }
    
    fn storage(mut self, storage: u32) -> Self {
        self.computer.storage = storage;
        self
    }
    
    fn gpu(mut self, gpu: impl Into<String>) -> Self {
        self.computer.gpu = Some(gpu.into());
        self
    }
    
    fn network_card(mut self, card: impl Into<String>) -> Self {
        self.computer.network_card = Some(card.into());
        self
    }
    
    fn build(self) -> Computer {
        self.computer
    }
}

// 使用示例
fn builder_example() {
    let basic_computer = ComputerBuilder::new()
        .cpu("Intel i5")
        .ram(8)
        .storage(512)
        .build();
    
    println!("基础电脑: {:?}", basic_computer);
    
    let gaming_computer = ComputerBuilder::new()
        .cpu("AMD Ryzen 9")
        .ram(32)
        .storage(2048)
        .gpu("NVIDIA RTX 4080")
        .network_card("Intel AX200")
        .build();
    
    println!("游戏电脑: {:?}", gaming_computer);
}
```

### 5. 原型模式（Prototype Pattern）

```rust
// 原型模式
trait Prototype: Clone {
    fn clone_box(&self) -> Box<dyn Prototype>;
    fn describe(&self) -> String;
}

impl<T> Prototype for T
where
    T: 'static + Clone + PrototypeClone,
{
    fn clone_box(&self) -> Box<dyn Prototype> {
        Box::new(self.clone())
    }
    
    fn describe(&self) -> String {
        self.prototype_describe()
    }
}

trait PrototypeClone: Clone {
    fn prototype_describe(&self) -> String;
}

#[derive(Clone)]
struct Circle {
    radius: f64,
    color: String,
}

impl Circle {
    fn new(radius: f64, color: impl Into<String>) -> Self {
        Circle {
            radius,
            color: color.into(),
        }
    }
}

impl PrototypeClone for Circle {
    fn prototype_describe(&self) -> String {
        format!("圆形 [半径: {}, 颜色: {}]", self.radius, self.color)
    }
}

#[derive(Clone)]
struct Rectangle {
    width: f64,
    height: f64,
    color: String,
}

impl Rectangle {
    fn new(width: f64, height: f64, color: impl Into<String>) -> Self {
        Rectangle {
            width,
            height,
            color: color.into(),
        }
    }
}

impl PrototypeClone for Rectangle {
    fn prototype_describe(&self) -> String {
        format!("矩形 [宽: {}, 高: {}, 颜色: {}]", self.width, self.height, self.color)
    }
}

// 原型管理器
struct ShapeRegistry {
    shapes: std::collections::HashMap<String, Box<dyn Prototype>>,
}

impl ShapeRegistry {
    fn new() -> Self {
        ShapeRegistry {
            shapes: std::collections::HashMap::new(),
        }
    }
    
    fn register(&mut self, name: impl Into<String>, prototype: Box<dyn Prototype>) {
        self.shapes.insert(name.into(), prototype);
    }
    
    fn create(&self, name: &str) -> Option<Box<dyn Prototype>> {
        self.shapes.get(name).map(|p| p.clone_box())
    }
}

// 使用示例
fn prototype_example() {
    let mut registry = ShapeRegistry::new();
    
    // 注册原型
    registry.register("小红圆", Box::new(Circle::new(5.0, "红色")));
    registry.register("大蓝矩形", Box::new(Rectangle::new(10.0, 5.0, "蓝色")));
    
    // 克隆原型
    if let Some(shape1) = registry.create("小红圆") {
        println!("克隆: {}", shape1.describe());
    }
    
    if let Some(shape2) = registry.create("大蓝矩形") {
        println!("克隆: {}", shape2.describe());
    }
}
```

## 二、结构型设计模式在 Rust 2024 中的实现

### 1. 适配器模式（Adapter Pattern）

```rust
// 适配器模式
// 目标接口
trait MediaPlayer {
    fn play(&self, file_type: &str, file_name: &str) -> String;
}

// 被适配的接口
trait AdvancedMediaPlayer {
    fn play_vlc(&self, file_name: &str) -> String;
    fn play_mp4(&self, file_name: &str) -> String;
}

// 具体被适配类
struct VlcPlayer;
impl AdvancedMediaPlayer for VlcPlayer {
    fn play_vlc(&self, file_name: &str) -> String {
        format!("播放VLC文件: {}", file_name)
    }
    
    fn play_mp4(&self, _: &str) -> String {
        "VlcPlayer不支持MP4".to_string()
    }
}

struct Mp4Player;
impl AdvancedMediaPlayer for Mp4Player {
    fn play_vlc(&self, _: &str) -> String {
        "Mp4Player不支持VLC".to_string()
    }
    
    fn play_mp4(&self, file_name: &str) -> String {
        format!("播放MP4文件: {}", file_name)
    }
}

// 适配器
struct MediaAdapter {
    advanced_player: Box<dyn AdvancedMediaPlayer>,
}

impl MediaAdapter {
    fn new(file_type: &str) -> Option<Self> {
        match file_type {
            "vlc" => Some(MediaAdapter {
                advanced_player: Box::new(VlcPlayer),
            }),
            "mp4" => Some(MediaAdapter {
                advanced_player: Box::new(Mp4Player),
            }),
            _ => None,
        }
    }
}

impl MediaPlayer for MediaAdapter {
    fn play(&self, file_type: &str, file_name: &str) -> String {
        match file_type {
            "vlc" => self.advanced_player.play_vlc(file_name),
            "mp4" => self.advanced_player.play_mp4(file_name),
            _ => format!("不支持的格式: {}", file_type),
        }
    }
}

// 客户端类
struct AudioPlayer;
impl MediaPlayer for AudioPlayer {
    fn play(&self, file_type: &str, file_name: &str) -> String {
        match file_type {
            "mp3" => format!("播放MP3文件: {}", file_name),
            "vlc" | "mp4" => {
                if let Some(adapter) = MediaAdapter::new(file_type) {
                    adapter.play(file_type, file_name)
                } else {
                    format!("不支持的格式: {}", file_type)
                }
            }
            _ => format!("不支持的格式: {}", file_type),
        }
    }
}

// 使用示例
fn adapter_example() {
    let player = AudioPlayer;
    
    println!("{}", player.play("mp3", "beyond_the_horizon.mp3"));
    println!("{}", player.play("mp4", "alone.mp4"));
    println!("{}", player.play("vlc", "far_far_away.vlc"));
    println!("{}", player.play("avi", "mind_me.avi"));
}
```

### 2. 桥接模式（Bridge Pattern）

```rust
// 桥接模式
// 实现部分接口
trait DrawingAPI {
    fn draw_circle(&self, x: f64, y: f64, radius: f64) -> String;
}

// 具体实现A
struct DrawingAPI1;
impl DrawingAPI {
    fn draw_circle(&self, x: f64, y: f64, radius: f64) -> String {
        format!("API1.圆形(x:{}, y:{}, 半径:{})", x, y, radius)
    }
}

// 具体实现B
struct DrawingAPI2;
impl DrawingAPI {
    fn draw_circle(&self, x: f64, y: f64, radius: f64) -> String {
        format!("API2.圆形(x:{}, y:{}, 半径:{})", x, y, radius)
    }
}

// 抽象部分
trait Shape {
    fn draw(&self) -> String;
    fn resize(&mut self, factor: f64);
}

// 精确抽象
struct Circle {
    x: f64,
    y: f64,
    radius: f64,
    drawing_api: Box<dyn DrawingAPI>,
}

impl Circle {
    fn new(x: f64, y: f64, radius: f64, drawing_api: Box<dyn DrawingAPI>) -> Self {
        Circle { x, y, radius, drawing_api }
    }
}

impl Shape for Circle {
    fn draw(&self) -> String {
        self.drawing_api.draw_circle(self.x, self.y, self.radius)
    }
    
    fn resize(&mut self, factor: f64) {
        self.radius *= factor;
    }
}

// 使用示例
fn bridge_example() {
    let mut circle1 = Circle::new(1.0, 2.0, 3.0, Box::new(DrawingAPI1));
    let mut circle2 = Circle::new(5.0, 7.0, 11.0, Box::new(DrawingAPI2));
    
    println!("{}", circle1.draw());
    circle1.resize(2.0);
    println!("调整大小后: {}", circle1.draw());
    
    println!("{}", circle2.draw());
    circle2.resize(0.5);
    println!("调整大小后: {}", circle2.draw());
}
```

### 3. 组合模式（Composite Pattern）

```rust
// 组合模式
trait Component {
    fn name(&self) -> &str;
    fn operation(&self) -> String;
    fn add(&mut self, component: Box<dyn Component>) -> Result<(), &'static str> {
        Err("不支持添加子组件")
    }
    fn remove(&mut self, name: &str) -> Result<(), &'static str> {
        Err("不支持移除子组件")
    }
    fn get_child(&self, name: &str) -> Option<&Box<dyn Component>> {
        None
    }
}

// 叶子组件
struct Leaf {
    name: String,
}

impl Leaf {
    fn new(name: impl Into<String>) -> Self {
        Leaf { name: name.into() }
    }
}

impl Component for Leaf {
    fn name(&self) -> &str {
        &self.name
    }
    
    fn operation(&self) -> String {
        format!("叶子 {} 的操作", self.name)
    }
}

// 复合组件
struct Composite {
    name: String,
    children: Vec<Box<dyn Component>>,
}

impl Composite {
    fn new(name: impl Into<String>) -> Self {
        Composite {
            name: name.into(),
            children: Vec::new(),
        }
    }
}

impl Component for Composite {
    fn name(&self) -> &str {
        &self.name
    }
    
    fn operation(&self) -> String {
        let mut result = format!("组合 {} 的操作:\n", self.name);
        for child in &self.children {
            result.push_str(&format!("- {}\n", child.operation()));
        }
        result
    }
    
    fn add(&mut self, component: Box<dyn Component>) -> Result<(), &'static str> {
        self.children.push(component);
        Ok(())
    }
    
    fn remove(&mut self, name: &str) -> Result<(), &'static str> {
        if let Some(index) = self.children.iter().position(|c| c.name() == name) {
            self.children.remove(index);
            Ok(())
        } else {
            Err("未找到子组件")
        }
    }
    
    fn get_child(&self, name: &str) -> Option<&Box<dyn Component>> {
        self.children.iter().find(|c| c.name() == name)
    }
}

// 使用示例
fn composite_example() {
    // 创建叶子节点
    let leaf1 = Box::new(Leaf::new("叶子1"));
    let leaf2 = Box::new(Leaf::new("叶子2"));
    let leaf3 = Box::new(Leaf::new("叶子3"));
    
    // 创建复合节点
    let mut composite1 = Composite::new("组合1");
    composite1.add(leaf1).unwrap();
    composite1.add(leaf2).unwrap();
    
    let mut composite2 = Composite::new("组合2");
    composite2.add(leaf3).unwrap();
    
    // 创建根节点
    let mut root = Composite::new("根");
    root.add(Box::new(composite1)).unwrap();
    root.add(Box::new(composite2)).unwrap();
    
    // 打印整个树结构
    println!("{}", root.operation());
    
    // 访问特定节点
    if let Some(comp1) = root.get_child("组合1") {
        println!("找到: {}", comp1.name());
    }
}
```

### 4. 装饰器模式（Decorator Pattern）

```rust
// 装饰器模式
trait Component {
    fn operation(&self) -> String;
}

// 具体组件
struct ConcreteComponent;
impl Component for ConcreteComponent {
    fn operation(&self) -> String {
        "ConcreteComponent".to_string()
    }
}

// 装饰器基类
struct Decorator {
    component: Box<dyn Component>,
}

impl Component for Decorator {
    fn operation(&self) -> String {
        self.component.operation()
    }
}

// 具体装饰器A
struct ConcreteDecoratorA {
    decorator: Decorator,
}

impl ConcreteDecoratorA {
    fn new(component: Box<dyn Component>) -> Self {
        ConcreteDecoratorA {
            decorator: Decorator { component },
        }
    }
    
    fn additional_operation(&self) -> String {
        "ConcreteDecoratorA的附加功能".to_string()
    }
}

impl Component for ConcreteDecoratorA {
    fn operation(&self) -> String {
        format!("{}，{}", self.decorator.operation(), self.additional_operation())
    }
}

// 具体装饰器B
struct ConcreteDecoratorB {
    decorator: Decorator,
}

impl ConcreteDecoratorB {
    fn new(component: Box<dyn Component>) -> Self {
        ConcreteDecoratorB {
            decorator: Decorator { component },
        }
    }
    
    fn additional_operation(&self) -> String {
        "ConcreteDecoratorB的附加功能".to_string()
    }
}

impl Component for ConcreteDecoratorB {
    fn operation(&self) -> String {
        format!("{}，{}", self.decorator.operation(), self.additional_operation())
    }
}

// 使用示例
fn decorator_example() {
    // 创建具体组件
    let component = Box::new(ConcreteComponent);
    println!("基础组件: {}", component.operation());
    
    // 使用装饰器A装饰
    let decorator_a = Box::new(ConcreteDecoratorA::new(component));
    println!("使用装饰器A: {}", decorator_a.operation());
    
    // 使用装饰器B装饰已装饰的组件
    let decorator_b = Box::new(ConcreteDecoratorB::new(decorator_a));
    println!("使用装饰器B: {}", decorator_b.operation());
}
```

### 5. 外观模式（Facade Pattern）

```rust
// 外观模式
// 复杂子系统组件
struct CPU {
    mode: String,
}

impl CPU {
    fn new() -> Self {
        CPU { mode: "正常".to_string() }
    }
    
    fn freeze(&mut self) {
        self.mode = "冻结".to_string();
        println!("CPU: 冻结");
    }
    
    fn jump(&self, position: u32) {
        println!("CPU: 跳转到位置 {}", position);
    }
    
    fn execute(&self) {
        println!("CPU: 执行指令");
    }
}

struct Memory {
    data: Vec<u8>,
}

impl Memory {
    fn new() -> Self {
        Memory { data: Vec::new() }
    }
    
    fn load(&mut self, position: u32, data: &[u8]) {
        println!("内存: 加载数据到位置 {}", position);
        // 简化实现
        self.data = data.to_vec();
    }
}

struct HardDrive {
    sectors: Vec<Vec<u8>>,
}

impl HardDrive {
    fn new() -> Self {
        HardDrive { sectors: vec![vec![0; 512]; 1000] }
    }
    
    fn read(&self, sector: u32, size: u32) -> Vec<u8> {
        println!("硬盘: 从扇区 {} 读取 {} 字节", sector, size);
        // 简化实现
        vec![1, 2, 3, 4]
    }
}

// 外观
struct ComputerFacade {
    cpu: CPU,
    memory: Memory,
    hard_drive: HardDrive,
}

impl ComputerFacade {
    fn new() -> Self {
        ComputerFacade {
            cpu: CPU::new(),
            memory: Memory::new(),
            hard_drive: HardDrive::new(),
        }
    }
    
    fn start(&mut self) {
        println!("计算机启动开始");
        self.cpu.freeze();
        let boot_sector = 0;
        let boot_size = 8;
        let boot_data = self.hard_drive.read(boot_sector, boot_size);
        self.memory.load(0, &boot_data);
        self.cpu.jump(0);
        self.cpu.execute();
        println!("计算机启动完成");
    }
}

// 使用示例
fn facade_example() {
    let mut computer = ComputerFacade::new();
    computer.start();
}
```

### 6. 享元模式（Flyweight Pattern）

```rust
// 享元模式
use std::collections::HashMap;

// 享元接口
trait TreeModel {
    fn render(&self, x: f64, y: f64, age: u32) -> String;
}

// 具体享元
struct TreeType {
    name: String,
    color: String,
    texture: String,
}

impl TreeType {
    fn new(name: impl Into<String>, color: impl Into<String>, texture: impl Into<String>) -> Self {
        TreeType {
            name: name.into(),
            color: color.into(),
            texture: texture.into(),
        }
    }
}

impl TreeModel for TreeType {
    fn render(&self, x: f64, y: f64, age: u32) -> String {
        format!(
            "在位置({}, {})渲染{}树，颜色:{}，纹理:{}，年龄:{}年",
            x, y, self.name, self.color, self.texture, age
        )
    }
}

// 享元工厂
struct TreeFactory {
    tree_types: HashMap<String, TreeType>,
}

impl TreeFactory {
    fn new() -> Self {
        TreeFactory {
            tree_types: HashMap::new(),
        }
    }
    
    fn get_tree_type(&mut self, name: &str, color: &str, texture: &str) -> &TreeType {
        let key = format!("{}:{}:{}", name, color, texture);
        
        if !self.tree_types.contains_key(&key) {
            println!("创建新的树类型: {}", key);
            self.tree_types.insert(
                key.clone(),
                TreeType::new(name, color, texture),
            );
        }
        
        self.tree_types.get(&key).unwrap()
    }
}

// 上下文类
struct Tree {
    x: f64,
    y: f64,
    age: u32,
    tree_type: *const TreeType, // 使用指针避免生命周期问题
}

impl Tree {
    fn new(x: f64, y: f64, age: u32, tree_type: &TreeType) -> Self {
        Tree {
            x,
            y,
            age,
            tree_type: tree_type as *const TreeType,
        }
    }
    
    fn render(&self) -> String {
        // 安全地从指针获取引用
        let tree_type = unsafe { &*self.tree_type };
        tree_type.render(self.x, self.y, self.age)
    }
}

// 使用示例
fn flyweight_example() {
    let mut forest = Vec::new();
    let mut factory = TreeFactory::new();
    
    // 创建森林
    for i in 0..5 {
        // 松树
        let pine = factory.get_tree_type("松树", "绿色", "松树皮");
        forest.push(Tree::new(i as f64 * 10.0, 0.0, 5 + i, pine));
        
        // 橡树
        let oak = factory.get_tree_type("橡树", "深绿色", "橡树皮");
        forest.push(Tree::new(i as f64 * 10.0, 20.0, 10 + i, oak));
    }
    
    // 渲染森林
    for (i, tree) in forest.iter().enumerate() {
        println!("树 #{}: {}", i, tree.render());
    }
}
```

### 7. 代理模式（Proxy Pattern）

```rust
// 代理模式
trait Image {
    fn display(&self) -> String;
}

// 实际主题
struct RealImage {
    filename: String,
}

impl RealImage {
    fn new(filename: impl Into<String>) -> Self {
        let filename = filename.into();
        println!("加载图片: {}", filename);
        RealImage { filename }
    }
    
    fn load_from_disk(&self) {
        println!("从磁盘加载: {}", self.filename);
    }
}

impl Image for RealImage {
    fn display(&self) -> String {
        format!("显示: {}", self.filename)
    }
}

// 代理
struct ProxyImage {
    filename: String,
    real_image: Option<RealImage>,
}

impl ProxyImage {
    fn new(filename: impl Into<String>) -> Self {
        ProxyImage {
            filename: filename.into(),
            real_image: None,
        }
    }
}

impl Image for ProxyImage {
    fn display(&self) -> String {
        // 懒加载 - 仅在需要时创建RealImage
        let real_image = match &self.real_image {
            Some(image) => image,
            None => {
                // 这里需要可变性，但trait方法是不可变的
                // 在实际代码中可以使用内部可变性（如RefCell）
                let this = unsafe { &mut *(self as *const Self as *mut Self) };
                this.real_image = Some(RealImage::new(&self.filename));
                this.real_image.as_ref().unwrap()
            }
        };
        
        real_image.display()
    }
}

// 使用示例
fn proxy_example() {
    // 使用代理
    let image = ProxyImage::new("test.jpg");
    
    // 图像将在首次显示时加载
    println!("首次调用:");
    println!("{}", image.display());
    
    // 图像不会再次加载
    println!("\n第二次调用:");
    println!("{}", image.display());
}
```

## 三、行为型设计模式在 Rust 2024 中的实现

### 1. 责任链模式（Chain of Responsibility Pattern）

```rust
// 责任链模式
enum LogLevel {
    Info,
    Debug,
    Error,
}

trait Logger {
    fn set_next(&mut self, logger: Box<dyn Logger>) -> Box<dyn Logger>;
    fn log_message(&self, level: LogLevel, message: &str) -> String;
    fn next(&self) -> Option<&Box<dyn Logger>>;
}

// 抽象记录器
struct AbstractLogger {
    level: LogLevel,
    next_logger: Option<Box<dyn Logger>>,
}

impl Logger for AbstractLogger {
    fn set_next(&mut self, logger: Box<dyn Logger>) -> Box<dyn Logger> {
        self.next_logger = Some(logger);
        Box::new(std::mem::replace(self, AbstractLogger {
            level: self.level,
            next_logger: None,
        }))
    }
    
    fn log_message(&self, level: LogLevel, message: &str) -> String {
        let mut result = String::new();
        
        // 检查当前记录器是否可以处理
        match (&self.level, &level) {
            (LogLevel::Info, _) => {
                result.push_str(&self.write(message));
            },
            (LogLevel::Debug, LogLevel::Debug | LogLevel::Error) => {
                result.push_str(&self.write(message));
            },
            (LogLevel::Error, LogLevel::Error) => {
                result.push_str(&self.write(message));
            },
            _ => {}
        }
        
        // 传递给下一个记录器
        if let Some(next) = &self.next_logger {
            result.push_str(&next.log_message(level, message));
        }
        
        result
    }
    
    fn next(&self) -> Option<&Box<dyn Logger>> {
        self.next_logger.as_ref()
    }
}

impl AbstractLogger {
    fn write(&self, message: &str) -> String {
        match self.level {
            LogLevel::Info => format!("信息: {}\n", message),
            LogLevel::Debug => format!("调试: {}\n", message),
            LogLevel::Error => format!("错误: {}\n", message),
        }
    }
}

// 具体记录器
struct InfoLogger {
    logger: AbstractLogger,
}

impl InfoLogger {
    fn new() -> Self {
        InfoLogger {
            logger: AbstractLogger {
                level: LogLevel::Info,
                next_logger: None,
            },
        }
    }
}

impl Logger for InfoLogger {
    fn set_next(&mut self, logger: Box<dyn Logger>) -> Box<dyn Logger> {
        self.logger.set_next(logger)
    }
    
    fn log_message(&self, level: LogLevel, message: &str) -> String {
        self.logger.log_message(level, message)
    }
    
    fn next(&self) -> Option<&Box<dyn Logger>> {
        self.logger.next()
    }
}

struct DebugLogger {
    logger: AbstractLogger,
}

impl DebugLogger {
    fn new() -> Self {
        DebugLogger {
            logger: AbstractLogger {
                level: LogLevel::Debug,
                next_logger: None,
            },
        }
    }
}

impl Logger for DebugLogger {
    fn set_next(&mut self, logger: Box<dyn Logger>) -> Box<dyn Logger> {
        self.logger.set_next(logger)
    }
    
    fn log_message(&self, level: LogLevel, message: &str) -> String {
        self.logger.log_message(level, message)
    }
    
    fn next(&self) -> Option<&Box<dyn Logger>> {
        self.logger.next()
    }
}

struct ErrorLogger {
    logger: AbstractLogger,
}

impl ErrorLogger {
    fn new() -> Self {
        ErrorLogger {
            logger: AbstractLogger {
                level: LogLevel::Error,
                next_logger: None,
            },
        }
    }
}

impl Logger for ErrorLogger {
    fn set_next(&mut self, logger: Box<dyn Logger>) -> Box<dyn Logger> {
        self.logger.set_next(logger)
    }
    
    fn log_message(&self, level: LogLevel, message: &str) -> String {
        self.logger.log_message(level, message)
    }
    
    fn next(&self) -> Option<&Box<dyn Logger>> {
        self.logger.next()
    }
}

// 使用示例
fn chain_of_responsibility_example() {
    // 创建责任链
    let mut error_logger = ErrorLogger::new();
    let mut debug_logger = DebugLogger::new();
    let info_logger = InfoLogger::new();
    
    debug_logger.set_next(Box::new(error_logger));
    let chain = info_logger.set_next(Box::new(debug_logger));
    
    // 记录消息
    println!("信息级别消息:");
    println!("{}", chain.log_message(LogLevel::Info, "这是一条信息"));
    
    println!("\n调试级别消息:");
    println!("{}", chain.log_message(LogLevel::Debug, "这是一条调试信息"));
    
    println!("\n错误级别消息:");
    println!("{}", chain.log_message(LogLevel::Error, "这是一条错误信息"));
}
```

### 2. 命令模式（Command Pattern）

```rust
// 命令模式
// 命令接口
trait Command {
    fn execute(&self) -> String;
}

// 接收者
struct Light {
    name: String,
    is_on: bool,
}

impl Light {
    fn new(name: impl Into<String>) -> Self {
        Light {
            name: name.into(),
            is_on: false,
        }
    }
    
    fn turn_on(&mut self) -> String {
        self.is_on = true;
        format!("{}灯已打开", self.name)
    }
    
    fn turn_off(&mut self) -> String {
        self.is_on = false;
        format!("{}灯已关闭", self.name)
    }
}

// 具体命令
struct LightOnCommand {
    light: std::rc::Rc<std::cell::RefCell<Light>>,
}

impl LightOnCommand {
    fn new(light: std::rc::Rc<std::cell::RefCell<Light>>) -> Self {
        LightOnCommand { light }
    }
}

impl Command for LightOnCommand {
    fn execute(&self) -> String {
        self.light.borrow_mut().turn_on()
    }
}

struct LightOffCommand {
    light: std::rc::Rc<std::cell::RefCell<Light>>,
}

impl LightOffCommand {
    fn new(light: std::rc::Rc<std::cell::RefCell<Light>>) -> Self {
        LightOffCommand { light }
    }
}

impl Command for LightOffCommand {
    fn execute(&self) -> String {
        self.light.borrow_mut().turn_off()
    }
}

// 调用者
struct RemoteControl {
    commands: std::collections::HashMap<String, Box<dyn Command>>,
}

impl RemoteControl {
    fn new() -> Self {
        RemoteControl {
            commands: std::collections::HashMap::new(),
        }
    }
    
    fn set_command(&mut self, button: impl Into<String>, command: Box<dyn Command>) {
        self.commands.insert(button.into(), command);
    }
    
    fn press_button(&self, button: &str) -> String {
        match self.commands.get(button) {
            Some(command) => command.execute(),
            None => format!("按钮 {} 未设置命令", button),
        }
    }
}

// 使用示例
fn command_example() {
    // 创建接收者
    let living_room_light = std::rc::Rc::new(std::cell::RefCell::new(Light::new("客厅")));
    let kitchen_light = std::rc::Rc::new(std::cell::RefCell::new(Light::new("厨房")));
    
    // 创建命令
    let living_room_light_on = Box::new(LightOnCommand::new(living_room_light.clone()));
    let living_room_light_off = Box::new(LightOffCommand::new(living_room_light));
    let kitchen_light_on = Box::new(LightOnCommand::new(kitchen_light.clone()));
    let kitchen_light_off = Box::new(LightOffCommand::new(kitchen_light));
    
    // 设置遥控器
    let mut remote = RemoteControl::new();
    remote.set_command("客厅开", living_room_light_on);
    remote.set_command("客厅关", living_room_light_off);
    remote.set_command("厨房开", kitchen_light_on);
    remote.set_command("厨房关", kitchen_light_off);
    
    // 使用遥控器
    println!("{}", remote.press_button("客厅开"));
    println!("{}", remote.press_button("厨房开"));
    println!("{}", remote.press_button("客厅关"));
    println!("{}", remote.press_button("厨房关"));
    println!("{}", remote.press_button("卧室开")); // 未设置的按钮
}
```

### 3. 解释器模式（Interpreter Pattern）

```rust
// 解释器模式
// 表达式接口
trait Expression {
    fn interpret(&self, context: &mut Context) -> bool;
}

// 上下文
struct Context {
    variables: std::collections::HashMap<String, bool>,
}

impl Context {
    fn new() -> Self {
        Context {
            variables: std::collections::HashMap::new(),
        }
    }
    
    fn set_variable(&mut self, name: impl Into<String>, value: bool) {
        self.variables.insert(name.into(), value);
    }
    
    fn get_variable(&self, name: &str) -> bool {
        *self.variables.get(name).unwrap_or(&false)
    }
}

// 终结符表达式
struct VariableExpression {
    name: String,
}

impl VariableExpression {
    fn new(name: impl Into<String>) -> Self {
        VariableExpression { name: name.into() }
    }
}

impl Expression for VariableExpression {
    fn interpret(&self, context: &mut Context) -> bool {
        context.get_variable(&self.name)
    }
}

// 非终结符表达式 - 与操作
struct AndExpression {
    expr1: Box<dyn Expression>,
    expr2: Box<dyn Expression>,
}

impl AndExpression {
    fn new(expr1: Box<dyn Expression>, expr2: Box<dyn Expression>) -> Self {
        AndExpression { expr1, expr2 }
    }
}

impl Expression for AndExpression {
    fn interpret(&self, context: &mut Context) -> bool {
        self.expr1.interpret(context) && self.expr2.interpret(context)
    }
}

// 非终结符表达式 - 或操作
struct OrExpression {
    expr1: Box<dyn Expression>,
    expr2: Box<dyn Expression>,
}

impl OrExpression {
    fn new(expr1: Box<dyn Expression>, expr2: Box<dyn Expression>) -> Self {
        OrExpression { expr1, expr2 }
    }
}

impl Expression for OrExpression {
    fn interpret(&self, context: &mut Context) -> bool {
        self.expr1.interpret(context) || self.expr2.interpret(context)
    }
}

// 非终结符表达式 - 非操作
struct NotExpression {
    expr: Box<dyn Expression>,
}

impl NotExpression {
    fn new(expr: Box<dyn Expression>) -> Self {
        NotExpression { expr }
    }
}

impl Expression for NotExpression {
    fn interpret(&self, context: &mut Context) -> bool {
        !self.expr.interpret(context)
    }
}

// 使用示例
fn interpreter_example() {
    // 规则: (A 和 B) 或 (A 和 C)
    let a = Box::new(VariableExpression::new("A"));
    let b = Box::new(VariableExpression::new("B"));
    let c = Box::new(VariableExpression::new("C"));
    
    let a_and_b = Box::new(AndExpression::new(
        Box::new(VariableExpression::new("A")),
        Box::new(VariableExpression::new("B")),
    ));
    
    let a_and_c = Box::new(AndExpression::new(
        Box::new(VariableExpression::new("A")),
        Box::new(VariableExpression::new("C")),
    ));
    
    let expression = OrExpression::new(a_and_b, a_and_c);
    
    // 创建上下文
    let mut context = Context::new();
    context.set_variable("A", true);
    context.set_variable("B", false);
    context.set_variable("C", true);
    
    // 解释表达式
    println!("A = true, B = false, C = true");
    println!("(A 和 B) 或 (A 和 C) = {}", expression.interpret(&mut context));
    
    // 修改上下文
    context.set_variable("B", true);
    println!("\nA = true, B = true, C = true");
    println!("(A 和 B) 或 (A 和 C) = {}", expression.interpret(&mut context));
}
```

### 4. 迭代器模式（Iterator Pattern）

```rust
// 迭代器模式
// 集合接口
trait Aggregate<T> {
    fn create_iterator(&self) -> Box<dyn Iterator<Item = &T>>;
}

// 具体集合
struct ConcreteAggregate<T> {
    items: Vec<T>,
}

impl<T> ConcreteAggregate<T> {
    fn new() -> Self {
        ConcreteAggregate { items: Vec::new() }
    }
    
    fn add_item(&mut self, item: T) {
        self.items.push(item);
    }
    
    fn get_items(&self) -> &[T] {
        &self.items
    }
}

impl<T> Aggregate<T> for ConcreteAggregate<T> {
    fn create_iterator(&self) -> Box<dyn Iterator<Item = &T>> {
        Box::new(self.items.iter())
    }
}

// 使用示例
fn iterator_example() {
    // 创建集合
    let mut aggregate = ConcreteAggregate::new();
    aggregate.add_item("项目 1".to_string());
    aggregate.add_item("项目 2".to_string());
    aggregate.add_item("项目 3".to_string());
    
    // 使用迭代器
    println!("使用迭代器遍历:");
    let iterator = aggregate.create_iterator();
    for item in iterator {
        println!("- {}", item);
    }
    
    // 使用Rust内置迭代器
    println!("\n使用Rust内置迭代器:");
    for item in aggregate.get_items() {
        println!("- {}", item);
    }
}
```

### 5. 中介者模式（Mediator Pattern）

```rust
// 中介者模式
use std::cell::RefCell;
use std::rc::{Rc, Weak};

// 中介者接口
trait Mediator {
    fn notify(&self, sender: &str, event: &str);
}

// 同事接口
trait Colleague {
    fn name(&self) -> &str;
    fn set_mediator(&mut self, mediator: Weak<RefCell<dyn Mediator>>);
    fn send(&self, event: &str);
    fn receive(&self, event: &str);
}

// 具体中介者
struct ConcreteMediator {
    colleagues: Vec<Rc<RefCell<dyn Colleague>>>,
}

impl ConcreteMediator {
    fn new() -> Self {
        ConcreteMediator {
            colleagues: Vec::new(),
        }
    }
    
    fn add_colleague(&mut self, colleague: Rc<RefCell<dyn Colleague>>) {
        let mediator_rc = Rc::new(RefCell::new(self as &dyn Mediator));
        let mediator_weak = Rc::downgrade(&mediator_rc);
        colleague.borrow_mut().set_mediator(mediator_weak);
        self.colleagues.push(colleague);
    }
}

impl Mediator for ConcreteMediator {
    fn notify(&self, sender: &str, event: &str) {
        for colleague in &self.colleagues {
            let name = colleague.borrow().name();
            if name != sender {
                colleague.borrow().receive(&format!("来自 {} 的消息: {}", sender, event));
            }
        }
    }
}

// 具体同事
struct ConcreteColleague {
    name: String,
    mediator: Option<Weak<RefCell<dyn Mediator>>>,
}

impl ConcreteColleague {
    fn new(name: impl Into<String>) -> Self {
        ConcreteColleague {
            name: name.into(),
            mediator: None,
        }
    }
}

impl Colleague for ConcreteColleague {
    fn name(&self) -> &str {
        &self.name
    }
    
    fn set_mediator(&mut self, mediator: Weak<RefCell<dyn Mediator>>) {
        self.mediator = Some(mediator);
    }
    
    fn send(&self, event: &str) {
        println!("{} 发送: {}", self.name, event);
        if let Some(mediator) = &self.mediator {
            if let Some(mediator) = mediator.upgrade() {
                mediator.borrow().notify(&self.name, event);
            }
        }
    }
    
    fn receive(&self, event: &str) {
        println!("{} 接收: {}", self.name, event);
    }
}

// 使用示例
fn mediator_example() {
    // 创建中介者
    let mut mediator = ConcreteMediator::new();
    
    // 创建同事
    let colleague1 = Rc::new(RefCell::new(ConcreteColleague::new("同事1")));
    let colleague2 = Rc::new(RefCell::new(ConcreteColleague::new("同事2")));
    let colleague3 = Rc::new(RefCell::new(ConcreteColleague::new("同事3")));
    
    // 添加同事到中介者
    mediator.add_colleague(colleague1.clone());
    mediator.add_colleague(colleague2.clone());
    mediator.add_colleague(colleague3.clone());
    
    // 同事之间通信
    colleague1.borrow().send("你好，大家好！");
    colleague2.borrow().send("收到，谢谢！");
}
```

### 6. 备忘录模式（Memento Pattern）

```rust
// 备忘录模式
// 备忘录
struct Memento {
    state: String,
}

impl Memento {
    fn new(state: impl Into<String>) -> Self {
        Memento { state: state.into() }
    }
    
    fn get_state(&self) -> &str {
        &self.state
    }
}

// 发起人
struct Originator {
    state: String,
}

impl Originator {
    fn new(state: impl Into<String>) -> Self {
        Originator { state: state.into() }
    }
    
    fn set_state(&mut self, state: impl Into<String>) {
        self.state = state.into();
    }
    
    fn get_state(&self) -> &str {
        &self.state
    }
    
    fn save_state_to_memento(&self) -> Memento {
        Memento::new(&self.state)
    }
    
    fn restore_state_from_memento(&mut self, memento: &Memento) {
        self.state = memento.get_state().to_string();
    }
}

// 管理者
struct Caretaker {
    mementos: Vec<Memento>,
}

impl Caretaker {
    fn new() -> Self {
        Caretaker { mementos: Vec::new() }
    }
    
    fn add_memento(&mut self, memento: Memento) {
        self.mementos.push(memento);
    }
    
    fn get_memento(&self, index: usize) -> Option<&Memento> {
        self.mementos.get(index)
    }
}

// 使用示例
fn memento_example() {
    let mut originator = Originator::new("状态 #1");
    let mut caretaker = Caretaker::new();
    
    // 保存初始状态
    caretaker.add_memento(originator.save_state_to_memento());
    println!("当前状态: {}", originator.get_state());
    
    // 修改状态并保存
    originator.set_state("状态 #2");
    caretaker.add_memento(originator.save_state_to_memento());
    println!("当前状态: {}", originator.get_state());
    
    // 再次修改状态并保存
    originator.set_state("状态 #3");
    caretaker.add_memento(originator.save_state_to_memento());
    println!("当前状态: {}", originator.get_state());
    
    // 恢复到第一个状态
    if let Some(memento) = caretaker.get_memento(0) {
        originator.restore_state_from_memento(memento);
        println!("恢复到状态: {}", originator.get_state());
    }
    
    // 恢复到第二个状态
    if let Some(memento) = caretaker.get_memento(1) {
        originator.restore_state_from_memento(memento);
        println!("恢复到状态: {}", originator.get_state());
    }
}
```

### 7. 观察者模式（Observer Pattern）

```rust
// 观察者模式
use std::cell::RefCell;
use std::rc::{Rc, Weak};

// 观察者接口
trait Observer {
    fn update(&self, message: &str);
}

// 主题接口
trait Subject {
    fn attach(&mut self, observer: Rc<RefCell<dyn Observer>>);
    fn detach(&mut self, observer: &Rc<RefCell<dyn Observer>>);
    fn notify(&self);
}

// 具体主题
struct ConcreteSubject {
    observers: Vec<Rc<RefCell<dyn Observer>>>,
    state: String,
}

impl ConcreteSubject {
    fn new() -> Self {
        ConcreteSubject {
            observers: Vec::new(),
            state: String::new(),
        }
    }
    
    fn set_state(&mut self, state: impl Into<String>) {
        self.state = state.into();
        self.notify();
    }
    
    fn get_state(&self) -> &str {
        &self.state
    }
}

impl Subject for ConcreteSubject {
    fn attach(&mut self, observer: Rc<RefCell<dyn Observer>>) {
        self.observers.push(observer);
    }
    
    fn detach(&mut self, observer: &Rc<RefCell<dyn Observer>>) {
        if let Some(index) = self.observers.iter().position(|o| Rc::ptr_eq(o, observer)) {
            self.observers.remove(index);
        }
    }
    
    fn notify(&self) {
        for observer in &self.observers {
            observer.borrow().update(&self.state);
        }
    }
}

// 具体观察者
struct ConcreteObserver {
    name: String,
    subject: Option<Weak<RefCell<ConcreteSubject>>>,
}

impl ConcreteObserver {
    fn new(name: impl Into<String>) -> Self {
        ConcreteObserver {
            name: name.into(),
            subject: None,
        }
    }
    
    fn set_subject(&mut self, subject: Weak<RefCell<ConcreteSubject>>) {
        self.subject = Some(subject);
    }
}

impl Observer for ConcreteObserver {
    fn update(&self, message: &str) {
        println!("观察者 {} 收到更新: {}", self.name, message);
    }
}

// 使用示例
fn observer_example() {
    // 创建主题
    let subject = Rc::new(RefCell::new(ConcreteSubject::new()));
    
    // 创建观察者
    let observer1 = Rc::new(RefCell::new(ConcreteObserver::new("观察者1")));
    let observer2 = Rc::new(RefCell::new(ConcreteObserver::new("观察者2")));
    
    // 设置观察者的主题
    observer1.borrow_mut().set_subject(Rc::downgrade(&subject));
    observer2.borrow_mut().set_subject(Rc::downgrade(&subject));
    
    // 添加观察者到主题
    subject.borrow_mut().attach(observer1.clone());
    subject.borrow_mut().attach(observer2.clone());
    
    // 改变主题状态
    subject.borrow_mut().set_state("第一次更新");
    
    // 移除一个观察者
    subject.borrow_mut().detach(&observer2);
    
    // 再次改变状态
    subject.borrow_mut().set_state("第二次更新");
}
```

### 8. 状态模式（State Pattern）

```rust
// 状态模式
// 状态接口
trait State {
    fn handle(&self) -> String;
    fn next(&self, context: &mut Context);
}

// 上下文
struct Context {
    state: Box<dyn State>,
}

impl Context {
    fn new(state: Box<dyn State>) -> Self {
        Context { state }
    }
    
    fn set_state(&mut self, state: Box<dyn State>) {
        self.state = state;
    }
    
    fn request(&mut self) -> String {
        let result = self.state.handle();
        self.state.next(self);
        result
    }
}

// 具体状态A
struct ConcreteStateA;
impl State for ConcreteStateA {
    fn handle(&self) -> String {
        "状态A的处理".to_string()
    }
    
    fn next(&self, context: &mut Context) {
        println!("从状态A转换到状态B");
        context.set_state(Box::new(ConcreteStateB));
    }
}

// 具体状态B
struct ConcreteStateB;
impl State for ConcreteStateB {
    fn handle(&self) -> String {
        "状态B的处理".to_string()
    }
    
    fn next(&self, context: &mut Context) {
        println!("从状态B转换到状态C");
        context.set_state(Box::new(ConcreteStateC));
    }
}

// 具体状态C
struct ConcreteStateC;
impl State for ConcreteStateC {
    fn handle(&self) -> String {
        "状态C的处理".to_string()
    }
    
    fn next(&self, context: &mut Context) {
        println!("从状态C转换回状态A");
        context.set_state(Box::new(ConcreteStateA));
    }
}

// 使用示例
fn state_example() {
    // 创建上下文，初始状态为A
    let mut context = Context::new(Box::new(ConcreteStateA));
    
    // 多次请求，状态会自动转换
    println!("结果: {}", context.request()); // 状态A -> B
    println!("结果: {}", context.request()); // 状态B -> C
    println!("结果: {}", context.request()); // 状态C -> A
    println!("结果: {}", context.request()); // 状态A -> B
}
```

### 9. 策略模式（Strategy Pattern）

```rust
// 策略模式
// 策略接口
trait Strategy {
    fn execute(&self, a: i32, b: i32) -> i32;
}

// 具体策略
struct AddStrategy;
impl Strategy for AddStrategy {
    fn execute(&self, a: i32, b: i32) -> i32 {
        a + b
    }
}

struct SubtractStrategy;
impl Strategy for SubtractStrategy {
    fn execute(&self, a: i32, b: i32) -> i32 {
        a - b
    }
}

struct MultiplyStrategy;
impl Strategy for MultiplyStrategy {
    fn execute(&self, a: i32, b: i32) -> i32 {
        a * b
    }
}

// 上下文
struct Context {
    strategy: Box<dyn Strategy>,
}

impl Context {
    fn new(strategy: Box<dyn Strategy>) -> Self {
        Context { strategy }
    }
    
    fn set_strategy(&mut self, strategy: Box<dyn Strategy>) {
        self.strategy = strategy;
    }
    
    fn execute_strategy(&self, a: i32, b: i32) -> i32 {
        self.strategy.execute(a, b)
    }
}

// 使用示例
fn strategy_example() {
    let a = 10;
    let b = 5;
    
    // 使用加法策略
    let mut context = Context::new(Box::new(AddStrategy));
    println!("{} + {} = {}", a, b, context.execute_strategy(a, b));
    
    // 切换到减法策略
    context.set_strategy(Box::new(SubtractStrategy));
    println!("{} - {} = {}", a, b, context.execute_strategy(a, b));
    
    // 切换到乘法策略
    context.set_strategy(Box::new(MultiplyStrategy));
    println!("{} * {} = {}", a, b, context.execute_strategy(a, b));
}
```

### 10. 模板方法模式（Template Method Pattern）

```rust
// 模板方法模式
// 抽象类
trait AbstractClass {
    // 模板方法
    fn template_method(&self) -> String {
        let mut result = String::new();
        
        result.push_str(&self.primitive_operation1());
        result.push_str("\n");
        result.push_str(&self.primitive_operation2());
        
        if self.hook() {
            result.push_str("\n");
            result.push_str("钩子方法被调用");
        }
        
        result
    }
    
    // 原语操作1 - 必须由子类实现
    fn primitive_operation1(&self) -> String;
    
    // 原语操作2 - 必须由子类实现
    fn primitive_operation2(&self) -> String;
    
    // 钩子方法 - 子类可选择性覆盖
    fn hook(&self) -> bool {
        false // 默认实现
    }
}

// 具体类A
struct ConcreteClassA;
impl AbstractClass for ConcreteClassA {
    fn primitive_operation1(&self) -> String {
        "ConcreteClassA: 实现操作1".to_string()
    }
    
    fn primitive_operation2(&self) -> String {
        "ConcreteClassA: 实现操作2".to_string()
    }
    
    // 不覆盖钩子方法，使用默认实现
}

// 具体类B
struct ConcreteClassB;
impl AbstractClass for ConcreteClassB {
    fn primitive_operation1(&self) -> String {
        "ConcreteClassB: 实现操作1".to_string()
    }
    
    fn primitive_operation2(&self) -> String {
        "ConcreteClassB: 实现操作2".to_string()
    }
    
    // 覆盖钩子方法
    fn hook(&self) -> bool {
        true
    }
}

// 使用示例
fn template_method_example() {
    // 使用具体类A
    let class_a = ConcreteClassA;
    println!("类A的结果:\n{}", class_a.template_method());
    
    // 使用具体类B
    let class_b = ConcreteClassB;
    println!("\n类B的结果:\n{}", class_b.template_method());
}
```

### 11. 访问者模式（Visitor Pattern）

```rust
// 访问者模式
// 元素接口
trait Element {
    fn accept(&self, visitor: &dyn Visitor);
}

// 访问者接口
trait Visitor {
    fn visit_concrete_element_a(&self, element: &ConcreteElementA);
    fn visit_concrete_element_b(&self, element: &ConcreteElementB);
}

// 具体元素A
struct ConcreteElementA {
    name: String,
}

impl ConcreteElementA {
    fn new(name: impl Into<String>) -> Self {
        ConcreteElementA { name: name.into() }
    }
    
    fn operation_a(&self) -> String {
        format!("元素A({})的操作", self.name)
    }
}

impl Element for ConcreteElementA {
    fn accept(&self, visitor: &dyn Visitor) {
        visitor.visit_concrete_element_a(self);
    }
}

// 具体元素B
struct ConcreteElementB {
    value: i32,
}

impl ConcreteElementB {
    fn new(value: i32) -> Self {
        ConcreteElementB { value }
    }
    
    fn operation_b(&self) -> String {
        format!("元素B({})的操作", self.value)
    }
}

impl Element for ConcreteElementB {
    fn accept(&self, visitor: &dyn Visitor) {
        visitor.visit_concrete_element_b(self);
    }
}

// 具体访问者1
struct ConcreteVisitor1;
impl Visitor for ConcreteVisitor1 {
    fn visit_concrete_element_a(&self, element: &ConcreteElementA) {
        println!("访问者1访问 {}", element.operation_a());
    }
    
    fn visit_concrete_element_b(&self, element: &ConcreteElementB) {
        println!("访问者1访问 {}", element.operation_b());
    }
}

// 具体访问者2
struct ConcreteVisitor2;
impl Visitor for ConcreteVisitor2 {
    fn visit_concrete_element_a(&self, element: &ConcreteElementA) {
        println!("访问者2访问 {}", element.operation_a());
    }
    
    fn visit_concrete_element_b(&self, element: &ConcreteElementB) {
        println!("访问者2访问 {}", element.operation_b());
    }
}

// 对象结构
struct ObjectStructure {
    elements: Vec<Box<dyn Element>>,
}

impl ObjectStructure {
    fn new() -> Self {
        ObjectStructure { elements: Vec::new() }
    }
    
    fn add_element(&mut self, element: Box<dyn Element>) {
        self.elements.push(element);
    }
    
    fn accept(&self, visitor: &dyn Visitor) {
        for element in &self.elements {
            element.accept(visitor);
        }
    }
}

// 使用示例
fn visitor_example() {
    // 创建对象结构
    let mut object_structure = ObjectStructure::new();
    
    // 添加元素
    object_structure.add_element(Box::new(ConcreteElementA::new("元素A1")));
    object_structure.add_element(Box::new(ConcreteElementB::new(42)));
    object_structure.add_element(Box::new(ConcreteElementA::new("元素A2")));
    
    // 创建访问者
    let visitor1 = ConcreteVisitor1;
    let visitor2 = ConcreteVisitor2;
    
    // 接受访问者1
    println!("访问者1访问:");
    object_structure.accept(&visitor1);
    
    // 接受访问者2
    println!("\n访问者2访问:");
    object_structure.accept(&visitor2);
}
```

## 四、Rust 2024 设计模式的表达能力分析

### 1. Rust 设计模式的独特优势

```rust
// Rust 2024 设计模式的独特优势示例

// 1. 所有权系统与设计模式的结合
struct ResourceOwner {
    data: Vec<u8>,
}

impl ResourceOwner {
    fn new(data: Vec<u8>) -> Self {
        ResourceOwner { data }
    }
    
    // 借用资源 - 不转移所有权
    fn borrow_resource(&self) -> &[u8] {
        &self.data
    }
    
    // 可变借用 - 允许修改但不转移所有权
    fn borrow_resource_mut(&mut self) -> &mut Vec<u8> {
        &mut self.data
    }
    
    // 消费资源 - 转移所有权
    fn consume(self) -> Vec<u8> {
        self.data
    }
}

// 2. 类型状态模式 - 利用类型系统在编译时保证状态转换安全
struct Draft {
    content: String,
}

impl Draft {
    fn new(content: impl Into<String>) -> Self {
        Draft { content: content.into() }
    }
    
    fn add_text(&mut self, text: &str) {
        self.content.push_str(text);
    }
    
    fn submit(self) -> PendingReview {
        PendingReview { content: self.content }
    }
}

struct PendingReview {
    content: String,
}

impl PendingReview {
    fn approve(self) -> Published {
        Published { content: self.content }
    }
    
    fn reject(self) -> Draft {
        Draft { content: self.content }
    }
}

struct Published {
    content: String,
}

impl Published {
    fn content(&self) -> &str {
        &self.content
    }
}

// 3. 特征对象与动态分派
trait Drawable {
    fn draw(&self) -> String;
}

struct Button {
    label: String,
}

impl Drawable for Button {
    fn draw(&self) -> String {
        format!("绘制按钮: {}", self.label)
    }
}

struct Image {
    path: String,
}

impl Drawable for Image {
    fn draw(&self) -> String {
        format!("绘制图片: {}", self.path)
    }
}

// 使用特征对象实现组合模式
struct Container {
    components: Vec<Box<dyn Drawable>>,
}

impl Container {
    fn new() -> Self {
        Container { components: Vec::new() }
    }
    
    fn add(&mut self, component: Box<dyn Drawable>) {
        self.components.push(component);
    }
}

impl Drawable for Container {
    fn draw(&self) -> String {
        let mut result = String::from("容器包含:\n");
        for component in &self.components {
            result.push_str(&format!("  {}\n", component.draw()));
        }
        result
    }
}

// 4. 零成本抽象与静态分派
struct Canvas<T: Drawable> {
    element: T,
}

impl<T: Drawable> Canvas<T> {
    fn new(element: T) -> Self {
        Canvas { element }
    }
    
    fn render(&self) -> String {
        format!("Canvas渲染: {}", self.element.draw())
    }
}
```

### 2. 与传统面向对象语言的设计模式对比

| 设计模式 | 传统OOP实现 | Rust 2024实现 | Rust优势 |
|:----:|:----|:----|:----|
| 单例模式 | 静态变量+私有构造函数 | 静态变量+懒加载 | 线程安全保证，编译时检查 |
| 工厂方法 | 继承+虚函数 | 特征+特征对象 | 更灵活的组合，无继承限制 |
| 观察者模式 | 接口+继承 | 特征+Rc/RefCell | 所有权明确，避免内存泄漏 |
| 策略模式 | 接口+多态 | 特征+闭包 | 函数式风格更简洁 |
| 装饰器模式 | 继承层次结构 | 组合+特征 | 更扁平的结构，避免继承爆炸 |
| 命令模式 | 接口+具体类 | 特征+闭包 | 可直接使用函数作为命令 |
| 状态模式 | 状态接口+具体状态 | 类型状态模式 | 编译时状态检查 |

### 3. Rust 2024 设计模式的表达能力分析

```rust
// Rust 2024 设计模式的表达能力示例

// 1. 函数式风格与设计模式的结合
// 使用函数式风格实现策略模式
type StrategyFn = Box<dyn Fn(i32, i32) -> i32>;

struct FunctionalContext {
    strategy: StrategyFn,
}

impl FunctionalContext {
    fn new(strategy: StrategyFn) -> Self {
        FunctionalContext { strategy }
    }
    
    fn execute(&self, a: i32, b: i32) -> i32 {
        (self.strategy)(a, b)
    }
}

// 使用示例
fn functional_strategy_example() {
    let a = 10;
    let b = 5;
    
    // 使用闭包定义策略
    let add_context = FunctionalContext::new(Box::new(|a, b| a + b));
    let subtract_context = FunctionalContext::new(Box::new(|a, b| a - b));
    let multiply_context = FunctionalContext::new(Box::new(|a, b| a * b));
    
    println!("函数式策略模式:");
    println!("{} + {} = {}", a, b, add_context.execute(a, b));
    println!("{} - {} = {}", a, b, subtract_context.execute(a, b));
    println!("{} * {} = {}", a, b, multiply_context.execute(a, b));
}

// 2. 组合优于继承的实现
// 使用组合实现装饰器模式
trait Logger {
    fn log(&self, message: &str) -> String;
}

struct ConsoleLogger;
impl Logger for ConsoleLogger {
    fn log(&self, message: &str) -> String {
        format!("控制台: {}", message)
    }
}

struct TimestampDecorator<T: Logger> {
    logger: T,
}

impl<T: Logger> TimestampDecorator<T> {
    fn new(logger: T) -> Self {
        TimestampDecorator { logger }
    }
}

impl<T: Logger> Logger for TimestampDecorator<T> {
    fn log(&self, message: &str) -> String {
        use std::time::{SystemTime, UNIX_EPOCH};
        let timestamp = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();
        
        self.logger.log(&format!("[{}] {}", timestamp, message))
    }
}

struct EncryptionDecorator<T: Logger> {
    logger: T,
}

impl<T: Logger> EncryptionDecorator<T> {
    fn new(logger: T) -> Self {
        EncryptionDecorator { logger }
    }
    
    fn encrypt(&self, message: &str) -> String {
        // 简单加密示例
        message.chars().map(|c| ((c as u8) + 1) as char).collect()
    }
}

impl<T: Logger> Logger for EncryptionDecorator<T> {
    fn log(&self, message: &str) -> String {
        let encrypted = self.encrypt(message);
        self.logger.log(&format!("加密: {}", encrypted))
    }
}

// 使用示例
fn composition_decorator_example() {
    let logger = ConsoleLogger;
    println!("{}", logger.log("基本日志"));
    
    let timestamp_logger = TimestampDecorator::new(ConsoleLogger);
    println!("{}", timestamp_logger.log("带时间戳的日志"));
    
    let encrypted_timestamp_logger = EncryptionDecorator::new(
        TimestampDecorator::new(ConsoleLogger)
    );
    println!("{}", encrypted_timestamp_logger.log("加密且带时间戳的日志"));
}
```

### 4. 多种等效设计方式的对比

```rust
// 多种等效设计方式对比

// 1. 命令模式的多种实现方式
// 方式1: 传统特征对象实现
trait Command {
    fn execute(&self) -> String;
}

struct ConcreteCommand {
    receiver: String,
}

impl ConcreteCommand {
    fn new(receiver: impl Into<String>) -> Self {
        ConcreteCommand { receiver: receiver.into() }
    }
}

impl Command for ConcreteCommand {
    fn execute(&self) -> String {
        format!("执行命令，接收者: {}", self.receiver)
    }
}

// 方式2: 函数指针实现
type CommandFn = fn() -> String;

// 方式3: 闭包实现
type CommandClosure = Box<dyn Fn() -> String>;

// 使用示例
fn command_pattern_comparison() {
    // 方式1: 特征对象
    let command1: Box<dyn Command> = Box::new(ConcreteCommand::new("接收者A"));
    
    // 方式2: 函数指针
    let command2: CommandFn = || "函数指针命令执行".to_string();
    
    // 方式3: 闭包
    let receiver = "接收者B".to_string();
    let command3: CommandClosure = Box::new(move || {
        format!("闭包命令执行，接收者: {}", receiver)
    });
    
    println!("命令模式比较:");
    println!("特征对象: {}", command1.execute());
    println!("函数指针: {}", command2());
    println!("闭包: {}", command3());
}

// 2. 工厂模式的多种实现方式
// 方式1: 传统工厂方法
trait Product {
    fn operation(&self) -> String;
}

struct ConcreteProductA;
impl Product for ConcreteProductA {
    fn operation(&self) -> String {
        "产品A的操作".to_string()
    }
}

struct ConcreteProductB;
impl Product for ConcreteProductB {
    fn operation(&self) -> String {
        "产品B的操作".to_string()
    }
}

trait Factory {
    fn create_product(&self) -> Box<dyn Product>;
}

struct ConcreteFactoryA;
impl Factory for ConcreteFactoryA {
    fn create_product(&self) -> Box<dyn Product> {
        Box::new(ConcreteProductA)
    }
}

// 方式2: 枚举工厂
enum ProductType {
    A,
    B,
}

struct EnumFactory;
impl EnumFactory {
    fn create_product(&self, product_type: ProductType) -> Box<dyn Product> {
        match product_type {
            ProductType::A => Box::new(ConcreteProductA),
            ProductType::B => Box::new(ConcreteProductB),
        }
    }
}

// 方式3: 函数式工厂
type ProductCreator = fn() -> Box<dyn Product>;

struct FunctionalFactory {
    creators: std::collections::HashMap<String, ProductCreator>,
}

impl FunctionalFactory {
    fn new() -> Self {
        let mut creators = std::collections::HashMap::new();
        creators.insert("A".to_string(), || Box::new(ConcreteProductA) as Box<dyn Product>);
        creators.insert("B".to_string(), || Box::new(ConcreteProductB) as Box<dyn Product>);
        
        FunctionalFactory { creators }
    }
    
    fn create_product(&self, product_type: &str) -> Option<Box<dyn Product>> {
        self.creators.get(product_type).map(|creator| creator())
    }
}

// 使用示例
fn factory_pattern_comparison() {
    // 方式1: 传统工厂方法
    let factory_a = ConcreteFactoryA;
    let product_a = factory_a.create_product();
    
    // 方式2: 枚举工厂
    let enum_factory = EnumFactory;
    let product_a2 = enum_factory.create_product(ProductType::A);
    let product_b2 = enum_factory.create_product(ProductType::B);
    
    // 方式3: 函数式工厂
    let functional_factory = FunctionalFactory::new();
    let product_a3 = functional_factory.create_product("A");
    
    println!("\n工厂模式比较:");
    println!("传统工厂: {}", product_a.operation());
    println!("枚举工厂A: {}", product_a2.operation());
    println!("枚举工厂B: {}", product_b2.operation());
    if let Some(product) = product_a3 {
        println!("函数式工厂: {}", product.operation());
    }
}
```

## 五、Rust 2024 设计模式的最佳实践

### 1. 设计模式选择指南

在 Rust 2024 中选择设计模式时，应考虑以下因素：

1. **所有权与生命周期**：选择与 Rust 所有权模型兼容的模式
2. **静态分派优先**：优先使用泛型和静态分派，仅在必要时使用动态分派
3. **组合优于继承**：使用组合和特征而非模拟继承层次结构
4. **利用类型系统**：使用 Rust 强大的类型系统编码设计约束
5. **考虑内存安全**：选择能保证内存安全的模式实现

### 2. 设计模式实现建议

```rust
// Rust 2024 设计模式实现建议

// 1. 使用泛型参数而非特征对象（当可行时）
// 不推荐: 使用特征对象
fn process_drawable_dyn(drawable: &dyn Drawable) {
    println!("{}", drawable.draw());
}

// 推荐: 使用泛型参数
fn process_drawable<T: Drawable>(drawable: &T) {
    println!("{}", drawable.draw());
}

// 2. 使用组合而非继承
// 不推荐: 模拟继承
trait Animal {
    fn make_sound(&self) -> String;
}

struct Dog {
    name: String,
}

impl Animal for Dog {
    fn make_sound(&self) -> String {
        format!("{} 说: 汪汪!", self.name)
    }
}

// 推荐: 使用组合
struct Animal2 {
    name: String,
}

impl Animal2 {
    fn make_sound(&self) -> String {
        format!("{} 发出声音", self.name)
    }
}

struct Dog2 {
    animal: Animal2,
    breed: String,
}

impl Dog2 {
    fn new(name: impl Into<String>, breed: impl Into<String>) -> Self {
        Dog2 {
            animal: Animal2 { name: name.into() },
            breed: breed.into(),
        }
    }
    
    fn make_sound(&self) -> String {
        format!("{}这只{}说: 汪汪!", self.animal.name, self.breed)
    }
}

// 3. 使用内部可变性谨慎处理可变性需求
use std::cell::RefCell;

struct Observer {
    name: String,
    observations: RefCell<Vec<String>>,
}

impl Observer {
    fn new(name: impl Into<String>) -> Self {
        Observer {
            name: name.into(),
            observations: RefCell::new(Vec::new()),
        }
    }
    
    fn observe(&self, event: impl Into<String>) {
        // 使用内部可变性修改状态
        self.observations.borrow_mut().push(event.into());
    }
    
    fn observations(&self) -> Vec<String> {
        self.observations.borrow().clone()
    }
}

// 4. 使用类型状态模式保证状态转换安全
enum ConnectionState {
    Disconnected,
    Connecting,
    Connected,
}

struct Connection<S> {
    state: S,
    address: String,
}

// 断开连接状态
struct Disconnected;

impl Connection<Disconnected> {
    fn new(address: impl Into<String>) -> Self {
        Connection {
            state: Disconnected,
            address: address.into(),
        }
    }
    
    fn connect(self) -> Connection<Connecting> {
        println!("开始连接到 {}", self.address);
        Connection {
            state: Connecting,
            address: self.address,
        }
    }
}

// 连接中状态
struct Connecting;

impl Connection<Connecting> {
    fn establish(self) -> Connection<Connected> {
        println!("已连接到 {}", self.address);
        Connection {
            state: Connected,
            address: self.address,
        }
    }
    
    fn timeout(self) -> Connection<Disconnected> {
        println!("连接超时");
        Connection {
            state: Disconnected,
            address: self.address,
        }
    }
}

// 已连接状态
struct Connected;

impl Connection<Connected> {
    fn send_data(&self, data: &str) {
        println!("发送数据到 {}: {}", self.address, data);
    }
    
    fn disconnect(self) -> Connection<Disconnected> {
        println!("断开与 {} 的连接", self.address);
        Connection {
            state: Disconnected,
            address: self.address,
        }
    }
}
```

### 3. 设计模式性能考量

在 Rust 2024 中实现设计模式时，应考虑以下性能因素：

1. **静态分派 vs 动态分派**：
   - 静态分派（泛型）：零运行时开销，但可能导致代码膨胀
   - 动态分派（特征对象）：运行时开销，但代码更紧凑

2. **内存布局**：
   - 避免不必要的间接引用
   - 考虑数据局部性和缓存友好性

3. **内部可变性成本**：
   - `RefCell` 有运行时检查开销
   - `Mutex` 和 `RwLock` 有同步开销

4. **所有权转移 vs 借用**：
   - 所有权转移可能导致不必要的克隆
   - 借用可能引入复杂的生命周期约束

```rust
// 设计模式性能考量示例

// 1. 静态分派 vs 动态分派性能对比
use std::time::{Duration, Instant};

// 使用特征对象（动态分派）
fn process_shapes_dynamic(shapes: &[Box<dyn Shape>]) -> f64 {
    shapes.iter().map(|s| s.area()).sum()
}

// 使用泛型和静态分派
fn process_shapes_static<T: Shape>(shapes: &[T]) -> f64 {
    shapes.iter().map(|s| s.area()).sum()
}

// 2. 内存布局优化
// 不优化的版本
struct ComponentManager {
    components: Vec<Box<dyn Component>>,
}

// 优化版本 - 使用枚举避免间接引用
enum ComponentEnum {
    Button(Button),
    Image(Image),
    Text(Text),
}

impl Component for ComponentEnum {
    fn render(&self) -> String {
        match self {
            ComponentEnum::Button(b) => b.render(),
            ComponentEnum::Image(i) => i.render(),
            ComponentEnum::Text(t) => t.render(),
        }
    }
}

struct OptimizedComponentManager {
    components: Vec<ComponentEnum>,
}

// 3. 内部可变性成本
// 高成本版本 - 每个组件都有Mutex
struct ThreadSafeComponent {
    data: std::sync::Mutex<String>,
}

// 优化版本 - 共享锁
struct OptimizedThreadSafeComponents {
    lock: std::sync::Mutex<()>,
    components: Vec<String>,
}

// 4. 所有权策略
// 高成本版本 - 频繁克隆
fn process_commands_cloning(commands: &[String]) -> Vec<String> {
    commands.iter().map(|cmd| {
        let mut cmd = cmd.clone();
        cmd.push_str("_processed");
        cmd
    }).collect()
}

// 优化版本 - 借用和原地修改
fn process_commands_borrowing(commands: &[String]) -> Vec<String> {
    commands.iter().map(|cmd| {
        let mut result = String::with_capacity(cmd.len() + 10);
        result.push_str(cmd);
        result.push_str("_processed");
        result
    }).collect()
}
```

### 4. 设计模式与 Rust 2024 新特性的结合

Rust 2024 引入了一些新特性，可以更优雅地实现设计模式：

1. **GAT (Generic Associated Types)**：更灵活地定义关联类型
2. **const 泛型**：编译时参数化
3. **异步特征**：支持异步设计模式
4. **类型别名 impl Trait**：简化复杂返回类型

```rust
// Rust 2024 新特性与设计模式结合

// 1. 使用GAT实现迭代器模式
trait Collection {
    type Item;
    type Iterator<'a>: Iterator<Item = &'a Self::Item>
    where
        Self: 'a;
    
    fn iter<'a>(&'a self) -> Self::Iterator<'a>;
}

struct MyCollection<T> {
    items: Vec<T>,
}

impl<T> Collection for MyCollection<T> {
    type Item = T;
    type Iterator<'a> = std::slice::Iter<'a, T> where T: 'a;
    
    fn iter<'a>(&'a self) -> Self::Iterator<'a> {
        self.items.iter()
    }
}

// 2. 使用const泛型实现编译时策略模式
enum StrategyType {
    Add,
    Subtract,
    Multiply,
}

struct ConstStrategy<const S: StrategyType>;

impl<const S: StrategyType> ConstStrategy<S> {
    fn execute(a: i32, b: i32) -> i32 {
        match S {
            StrategyType::Add => a + b,
            StrategyType::Subtract => a - b,
            StrategyType::Multiply => a * b,
        }
    }
}

// 3. 异步工厂模式
trait AsyncFactory {
    async fn create_product(&self) -> Box<dyn Product>;
}

struct AsyncConcreteFactory;
impl AsyncFactory for AsyncConcreteFactory {
    async fn create_product(&self) -> Box<dyn Product> {
        // 模拟异步操作
        tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
        Box::new(ConcreteProductA)
    }
}

// 4. 使用类型别名impl Trait简化工厂返回类型
type ProductResult = impl Product;

fn simplified_factory(product_type: &str) -> ProductResult {
    match product_type {
        "A" => ConcreteProductA,
        _ => ConcreteProductB,
    }
}
```

## 六、结论：Rust 2024 设计模式的未来展望

### 1. Rust 设计模式的演进趋势

随着 Rust 语言的不断发展，设计模式也在不断演进：

1. **更函数式的实现**：利用闭包和高阶函数简化设计模式
2. **编译时保证**：更多地利用类型系统在编译时保证正确性
3. **零成本抽象**：追求无运行时开销的设计模式实现
4. **异步设计模式**：适应异步编程范式的设计模式变体
5. **领域特定模式**：针对 Rust 生态系统特定领域的专用模式

### 2. Rust 与其他语言设计模式的比较总结

| 特性 | Rust 2024 | Java/C++ | JavaScript/TypeScript | Go |
|:----:|:----|:----|:----|:----|
| 继承支持 | 无继承，使用组合 | 类继承 | 原型/类继承 | 无继承，使用组合 |
| 多态实现 | 特征 | 接口/虚函数 | 鸭子类型/接口 | 接口 |
| 泛型支持 | 强大的静态泛型 | 类型擦除泛型 | 动态类型/泛型 | 有限的泛型 |
| 内存管理 | 所有权系统 | 垃圾回收/手动 | 垃圾回收 | 垃圾回收 |
| 并发安全 | 编译时保证 | 同步原语 | 异步/回调 | Goroutines |
| 函数式特性 | 闭包和高阶函数 | 有限支持 | 一等公民 | 有限支持 |

### 3. 最终建议

在 Rust 2024 中实现设计模式时，应遵循以下原则：

1. **拥抱 Rust 哲学**：不要强行套用其他语言的模式，而应适应 Rust 的所有权模型和类型系统
2. **组合优于继承**：使用组合和特征而非模拟继承层次结构
3. **静态优于动态**：优先使用编译时多态（泛型），仅在必要时使用运行时多态（特征对象）
4. **类型驱动设计**：利用 Rust 的类型系统编码设计约束和不变量
5. **平衡抽象与性能**：在抽象和性能之间找到平衡点
6. **考虑并发**：设计时考虑并发安全性和可组合性
7. **利用新特性**：积极采用 Rust 2024 的新特性改进设计模式实现

```rust
// 最终示例：Rust 2024 风格的命令模式实现

// 定义命令特征
trait Command {
    fn execute(&self) -> String;
}

// 使用闭包实现命令
struct ClosureCommand<F>
where
    F: Fn() -> String,
{
    execute_fn: F,
}

impl<F> ClosureCommand<F>
where
    F: Fn() -> String,
{
    fn new(execute_fn: F) -> Self {
        ClosureCommand { execute_fn }
    }
}

impl<F> Command for ClosureCommand<F>
where
    F: Fn() -> String,
{
    fn execute(&self) -> String {
        (self.execute_fn)()
    }
}

// 命令调用者
struct Invoker {
    commands: std::collections::HashMap<String, Box<dyn Command>>,
}

impl Invoker {
    fn new() -> Self {
        Invoker {
            commands: std::collections::HashMap::new(),
        }
    }
    
    fn register<C: Command + 'static>(&mut self, name: impl Into<String>, command: C) {
        self.commands.insert(name.into(), Box::new(command));
    }
    
    fn execute(&self, name: &str) -> Option<String> {
        self.commands.get(name).map(|cmd| cmd.execute())
    }
}

// 使用示例
fn final_example() {
    let mut invoker = Invoker::new();
    
    // 使用闭包创建命令
    invoker.register("简单命令", ClosureCommand::new(|| {
        "执行简单命令".to_string()
    }));
    
    // 捕获环境的命令
    let counter = std::cell::RefCell::new(0);
    invoker.register("计数命令", ClosureCommand::new(move || {
        let mut count = counter.borrow_mut();
        *count += 1;
        format!("计数命令执行 {} 次", *count)
    }));
    
    // 执行命令
    if let Some(result) = invoker.execute("简单命令") {
        println!("结果: {}", result);
    }
    
    if let Some(result) = invoker.execute("计数命令") {
        println!("结果: {}", result);
    }
    
    if let Some(result) = invoker.execute("计数命令") {
        println!("结果: {}", result);
    }
}
```

总结来说，Rust 2024 提供了强大而灵活的工具来实现各种设计模式，同时保持了内存安全、并发安全和高性能的特点。
通过理解 Rust 的独特优势和设计哲学，开发者可以创建出既符合设计模式原则又充分利用 Rust 语言特性的优雅解决方案。
