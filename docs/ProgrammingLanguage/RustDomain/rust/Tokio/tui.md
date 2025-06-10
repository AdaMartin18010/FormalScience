# Rust实现异步交互式控制台

下面是一个使用 Rust 2024 结合 ratatui (之前的 tui-rs) 实现的交互式控制台应用示例，用于展示程序的指标和状态。

## 目录

- [Rust实现异步交互式控制台](#rust实现异步交互式控制台)
  - [目录](#目录)
  - [1. 项目依赖配置](#1-项目依赖配置)
  - [2. 基础 UI 框架实现](#2-基础-ui-框架实现)
  - [3. 指标状态管理](#3-指标状态管理)
  - [4. UI 渲染实现](#4-ui-渲染实现)
  - [5. 交互控制实现](#5-交互控制实现)
  - [6. 帮助菜单实现](#6-帮助菜单实现)
  - [7. 指标收集器实现](#7-指标收集器实现)
  - [8. 主程序实现](#8-主程序实现)
  - [9. 自定义图表实现](#9-自定义图表实现)
  - [10. 配置文件支持](#10-配置文件支持)

## 1. 项目依赖配置

```toml
[dependencies]
tokio = { version = "1.0", features = ["full"] }
ratatui = "0.24"
crossterm = "0.27"
metrics = "0.21"
metrics-runtime = "0.21"
metrics-util = "0.15"
chrono = "0.4"
anyhow = "1.0"
futures = "0.3"
async-trait = "0.1"
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"
```

## 2. 基础 UI 框架实现

```rust
use ratatui::{
    backend::CrosstermBackend,
    layout::{Constraint, Direction, Layout},
    style::{Color, Modifier, Style},
    widgets::{Block, Borders, Chart, Dataset, Paragraph},
    Terminal,
};
use crossterm::{
    event::{self, DisableMouseCapture, EnableMouseCapture, Event, KeyCode},
    execute,
    terminal::{disable_raw_mode, enable_raw_mode, EnterAlternateScreen, LeaveAlternateScreen},
};

pub struct App {
    metrics: MetricsState,
    should_quit: bool,
}

impl App {
    pub fn new() -> Self {
        Self {
            metrics: MetricsState::default(),
            should_quit: false,
        }
    }

    pub fn on_key(&mut self, key: KeyCode) {
        match key {
            KeyCode::Char('q') => self.should_quit = true,
            _ => {}
        }
    }
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 设置终端
    enable_raw_mode()?;
    let mut stdout = std::io::stdout();
    execute!(stdout, EnterAlternateScreen, EnableMouseCapture)?;
    let backend = CrosstermBackend::new(stdout);
    let mut terminal = Terminal::new(backend)?;

    // 创建应用状态
    let mut app = App::new();

    // 运行事件循环
    loop {
        terminal.draw(|f| ui(f, &app))?;

        if event::poll(std::time::Duration::from_millis(100))? {
            if let Event::Key(key) = event::read()? {
                app.on_key(key.code);
            }
        }

        if app.should_quit {
            break;
        }

        // 更新指标
        app.metrics.update().await;
    }

    // 清理终端
    disable_raw_mode()?;
    execute!(
        terminal.backend_mut(),
        LeaveAlternateScreen,
        DisableMouseCapture
    )?;
    terminal.show_cursor()?;

    Ok(())
}
```

## 3. 指标状态管理

```rust
use std::collections::VecDeque;
use chrono::{DateTime, Local};

#[derive(Default)]
pub struct MetricsState {
    cpu_usage: VecDeque<(f64, f64)>,
    memory_usage: VecDeque<(f64, f64)>,
    request_count: u64,
    error_count: u64,
    last_update: Option<DateTime<Local>>,
}

impl MetricsState {
    pub fn new() -> Self {
        Self {
            cpu_usage: VecDeque::with_capacity(100),
            memory_usage: VecDeque::with_capacity(100),
            request_count: 0,
            error_count: 0,
            last_update: None,
        }
    }

    pub async fn update(&mut self) {
        let now = Local::now();
        let timestamp = now.timestamp() as f64;

        // 更新 CPU 使用率
        if let Ok(cpu) = sys_info::cpu_load_aggregate() {
            self.cpu_usage.push_back((timestamp, cpu.user * 100.0));
            if self.cpu_usage.len() > 100 {
                self.cpu_usage.pop_front();
            }
        }

        // 更新内存使用率
        if let Ok(mem) = sys_info::mem_info() {
            let usage = (mem.total - mem.free) as f64 / mem.total as f64 * 100.0;
            self.memory_usage.push_back((timestamp, usage));
            if self.memory_usage.len() > 100 {
                self.memory_usage.pop_front();
            }
        }

        self.last_update = Some(now);
    }
}
```

## 4. UI 渲染实现

```rust
fn ui<B: Backend>(f: &mut Frame<B>, app: &App) {
    // 创建主布局
    let chunks = Layout::default()
        .direction(Direction::Vertical)
        .margin(1)
        .constraints([
            Constraint::Length(3),
            Constraint::Min(10),
            Constraint::Length(3),
        ])
        .split(f.size());

    // 渲染标题
    let title = Paragraph::new("System Metrics Dashboard")
        .style(Style::default().fg(Color::Cyan))
        .block(Block::default().borders(Borders::ALL));
    f.render_widget(title, chunks[0]);

    // 渲染图表
    let charts_layout = Layout::default()
        .direction(Direction::Horizontal)
        .constraints([Constraint::Percentage(50), Constraint::Percentage(50)])
        .split(chunks[1]);

    // CPU 使用率图表
    let cpu_dataset = Dataset::default()
        .name("CPU Usage")
        .marker(symbols::Marker::Braille)
        .style(Style::default().fg(Color::Green))
        .data(&app.metrics.cpu_usage.iter().map(|&(x, y)| (x, y)).collect::<Vec<_>>());

    let cpu_chart = Chart::new(vec![cpu_dataset])
        .block(Block::default().title("CPU Usage (%)").borders(Borders::ALL))
        .x_axis(
            Axis::default()
                .title("Time")
                .style(Style::default().fg(Color::Gray))
                .bounds([
                    app.metrics.cpu_usage.front().map(|&(x, _)| x).unwrap_or(0.0),
                    app.metrics.cpu_usage.back().map(|&(x, _)| x).unwrap_or(100.0),
                ]),
        )
        .y_axis(
            Axis::default()
                .title("Usage")
                .style(Style::default().fg(Color::Gray))
                .bounds([0.0, 100.0]),
        );
    f.render_widget(cpu_chart, charts_layout[0]);

    // 内存使用率图表
    let memory_dataset = Dataset::default()
        .name("Memory Usage")
        .marker(symbols::Marker::Braille)
        .style(Style::default().fg(Color::Blue))
        .data(&app.metrics.memory_usage.iter().map(|&(x, y)| (x, y)).collect::<Vec<_>>());

    let memory_chart = Chart::new(vec![memory_dataset])
        .block(Block::default().title("Memory Usage (%)").borders(Borders::ALL))
        .x_axis(
            Axis::default()
                .title("Time")
                .style(Style::default().fg(Color::Gray))
                .bounds([
                    app.metrics.memory_usage.front().map(|&(x, _)| x).unwrap_or(0.0),
                    app.metrics.memory_usage.back().map(|&(x, _)| x).unwrap_or(100.0),
                ]),
        )
        .y_axis(
            Axis::default()
                .title("Usage")
                .style(Style::default().fg(Color::Gray))
                .bounds([0.0, 100.0]),
        );
    f.render_widget(memory_chart, charts_layout[1]);

    // 渲染状态栏
    let status = format!(
        "Requests: {} | Errors: {} | Last Update: {}",
        app.metrics.request_count,
        app.metrics.error_count,
        app.metrics.last_update.map_or("Never".to_string(), |dt| dt.format("%H:%M:%S").to_string())
    );
    let status_bar = Paragraph::new(status)
        .style(Style::default().fg(Color::White))
        .block(Block::default().borders(Borders::ALL));
    f.render_widget(status_bar, chunks[2]);
}
```

## 5. 交互控制实现

```rust
use crossterm::event::KeyModifiers;

#[derive(Debug, Clone)]
pub enum Action {
    Quit,
    ToggleChart,
    Refresh,
    Help,
}

pub struct InputHandler {
    actions: Vec<Action>,
}

impl InputHandler {
    pub fn new() -> Self {
        Self {
            actions: Vec::new(),
        }
    }

    pub fn handle_input(&mut self, event: Event) {
        match event {
            Event::Key(key) => {
                match (key.code, key.modifiers) {
                    (KeyCode::Char('q'), _) => self.actions.push(Action::Quit),
                    (KeyCode::Char('c'), KeyModifiers::CONTROL) => self.actions.push(Action::Quit),
                    (KeyCode::Char('h'), _) => self.actions.push(Action::Help),
                    (KeyCode::Char('r'), _) => self.actions.push(Action::Refresh),
                    (KeyCode::Tab, _) => self.actions.push(Action::ToggleChart),
                    _ => {}
                }
            }
            _ => {}
        }
    }

    pub fn next_action(&mut self) -> Option<Action> {
        self.actions.pop()
    }
}
```

## 6. 帮助菜单实现

```rust
pub struct HelpMenu {
    visible: bool,
}

impl HelpMenu {
    pub fn new() -> Self {
        Self { visible: false }
    }

    pub fn toggle(&mut self) {
        self.visible = !self.visible;
    }

    pub fn render<B: Backend>(&self, f: &mut Frame<B>, area: Rect) {
        if !self.visible {
            return;
        }

        let help_text = vec![
            "Help Menu",
            "",
            "q, Ctrl+c - Quit",
            "h - Toggle help",
            "r - Refresh data",
            "Tab - Toggle between charts",
        ];

        let block = Block::default()
            .title("Help")
            .borders(Borders::ALL)
            .style(Style::default().bg(Color::Black));

        let text = Text::from(help_text.join("\n"));
        let paragraph = Paragraph::new(text)
            .block(block)
            .wrap(Wrap { trim: true });

        let area = centered_rect(60, 40, area);
        f.render_widget(Clear, area);
        f.render_widget(paragraph, area);
    }
}
```

## 7. 指标收集器实现

```rust
use metrics::{Counter, Gauge, Histogram};
use std::sync::Arc;

pub struct MetricsCollector {
    registry: Arc<Registry>,
    request_counter: Counter,
    error_counter: Counter,
    response_time: Histogram,
    cpu_gauge: Gauge,
    memory_gauge: Gauge,
}

impl MetricsCollector {
    pub fn new() -> Self {
        let registry = Arc::new(Registry::new());
        
        let request_counter = Counter::new("requests_total");
        let error_counter = Counter::new("errors_total");
        let response_time = Histogram::new("response_time_seconds");
        let cpu_gauge = Gauge::new("cpu_usage_percent");
        let memory_gauge = Gauge::new("memory_usage_percent");

        registry.register("requests_total", &request_counter);
        registry.register("errors_total", &error_counter);
        registry.register("response_time_seconds", &response_time);
        registry.register("cpu_usage_percent", &cpu_gauge);
        registry.register("memory_usage_percent", &memory_gauge);

        Self {
            registry,
            request_counter,
            error_counter,
            response_time,
            cpu_gauge,
            memory_gauge,
        }
    }

    pub fn record_request(&self) {
        self.request_counter.increment(1);
    }

    pub fn record_error(&self) {
        self.error_counter.increment(1);
    }

    pub fn record_response_time(&self, duration: f64) {
        self.response_time.record(duration);
    }

    pub fn update_cpu_usage(&self, usage: f64) {
        self.cpu_gauge.set(usage);
    }

    pub fn update_memory_usage(&self, usage: f64) {
        self.memory_gauge.set(usage);
    }
}
```

## 8. 主程序实现

```rust
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化终端
    let terminal = setup_terminal()?;
    
    // 创建应用状态
    let app = App::new();
    let metrics_collector = Arc::new(MetricsCollector::new());
    let input_handler = InputHandler::new();
    let help_menu = HelpMenu::new();

    // 启动指标收集任务
    let metrics_task = {
        let metrics_collector = metrics_collector.clone();
        tokio::spawn(async move {
            loop {
                collect_system_metrics(&metrics_collector).await;
                tokio::time::sleep(Duration::from_secs(1)).await;
            }
        })
    };

    // 运行主事件循环
    run_app(terminal, app, metrics_collector, input_handler, help_menu).await?;

    // 清理
    cleanup_terminal()?;
    metrics_task.abort();

    Ok(())
}

async fn run_app(
    mut terminal: Terminal<CrosstermBackend<Stdout>>,
    mut app: App,
    metrics_collector: Arc<MetricsCollector>,
    mut input_handler: InputHandler,
    mut help_menu: HelpMenu,
) -> Result<(), Box<dyn std::error::Error>> {
    loop {
        // 渲染 UI
        terminal.draw(|f| {
            let size = f.size();
            ui(f, &app, &help_menu, size);
        })?;

        // 处理输入
        if event::poll(Duration::from_millis(100))? {
            let event = event::read()?;
            input_handler.handle_input(event);
        }

        // 处理动作
        while let Some(action) = input_handler.next_action() {
            match action {
                Action::Quit => return Ok(()),
                Action::Help => help_menu.toggle(),
                Action::Refresh => app.metrics.update().await,
                Action::ToggleChart => app.toggle_chart(),
            }
        }

        // 更新指标
        app.update_metrics(metrics_collector.as_ref());
    }
}
```

## 9. 自定义图表实现

```rust
pub struct CustomChart {
    title: String,
    data: VecDeque<(f64, f64)>,
    style: Style,
    max_points: usize,
}

impl CustomChart {
    pub fn new(title: &str, max_points: usize) -> Self {
        Self {
            title: title.to_string(),
            data: VecDeque::with_capacity(max_points),
            style: Style::default().fg(Color::Cyan),
            max_points,
        }
    }

    pub fn add_point(&mut self, x: f64, y: f64) {
        self.data.push_back((x, y));
        if self.data.len() > self.max_points {
            self.data.pop_front();
        }
    }

    pub fn render<B: Backend>(&self, f: &mut Frame<B>, area: Rect) {
        let dataset = Dataset::default()
            .name(&self.title)
            .marker(symbols::Marker::Braille)
            .style(self.style)
            .data(&self.data.iter().map(|&(x, y)| (x, y)).collect::<Vec<_>>());

        let chart = Chart::new(vec![dataset])
            .block(Block::default().title(&self.title).borders(Borders::ALL))
            .x_axis(
                Axis::default()
                    .title("Time")
                    .style(Style::default().fg(Color::Gray))
                    .bounds([
                        self.data.front().map(|&(x, _)| x).unwrap_or(0.0),
                        self.data.back().map(|&(x, _)| x).unwrap_or(100.0),
                    ]),
            )
            .y_axis(
                Axis::default()
                    .title("Value")
                    .style(Style::default().fg(Color::Gray))
                    .bounds([0.0, 100.0]),
            );

        f.render_widget(chart, area);
    }
}
```

## 10. 配置文件支持

```rust
use serde::Deserialize;
use std::fs;

#[derive(Deserialize)]
pub struct Config {
    pub update_interval: u64,
    pub max_points: usize,
    pub charts: Vec<ChartConfig>,
    pub colors: ColorConfig,
}

#[derive(Deserialize)]
pub struct ChartConfig {
    pub title: String,
    pub metric: String,
    pub color: String,
}

#[derive(Deserialize)]
pub struct ColorConfig {
    pub background: String,
    pub foreground: String,
    pub accent: String,
}

impl Config {
    pub fn load(path: &str) -> Result<Self, Box<dyn std::error::Error>> {
        let content = fs::read_to_string(path)?;
        Ok(toml::from_str(&content)?)
    }
}
```

这个完整的示例展示了如何：

1. 创建交互式控制台界面
2. 实现实时指标展示
3. 支持键盘快捷键
4. 提供帮助菜单
5. 收集和显示系统指标
6. 自定义图表渲染
7. 配置文件支持

通过这种方式，您可以构建一个功能丰富的控制台应用程序，用于监控和展示程序的各种指标。
