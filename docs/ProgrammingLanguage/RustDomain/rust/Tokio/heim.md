# Rust 2024 + Tokio + Heim + OpenTelemetry 实现的分布式监控系统

我将为您展示一个使用 Rust 2024 + Tokio + Heim + OpenTelemetry 实现的分布式监控系统。

## 目录

- [Rust 2024 + Tokio + Heim + OpenTelemetry 实现的分布式监控系统](#rust-2024--tokio--heim--opentelemetry-实现的分布式监控系统)
  - [目录](#目录)
  - [1. 项目依赖配置](#1-项目依赖配置)
  - [2. 系统指标收集器实现](#2-系统指标收集器实现)
  - [3. 分布式追踪实现](#3-分布式追踪实现)
  - [4. 指标控制器实现](#4-指标控制器实现)
  - [5. gRPC 服务实现](#5-grpc-服务实现)
  - [6. 指标聚合器实现](#6-指标聚合器实现)
  - [7. 告警系统实现](#7-告警系统实现)
  - [8. 存储系统实现](#8-存储系统实现)
  - [9. 主程序实现](#9-主程序实现)
  - [10. 配置文件示例](#10-配置文件示例)

## 1. 项目依赖配置

```toml
[dependencies]
tokio = { version = "1.0", features = ["full"] }
heim = { version = "0.1.0-rc.1", features = ["full"] }
opentelemetry = { version = "0.21", features = ["rt-tokio"] }
opentelemetry-otlp = { version = "0.14", features = ["metrics"] }
opentelemetry_sdk = { version = "0.21", features = ["rt-tokio"] }
tonic = "0.10"
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"
tracing = "0.1"
tracing-opentelemetry = "0.22"
anyhow = "1.0"
async-trait = "0.1"
dashmap = "5.5"
metrics = "0.21"
metrics-exporter-prometheus = "0.12"
chrono = { version = "0.4", features = ["serde"] }
```

## 2. 系统指标收集器实现

```rust
use heim::cpu::CpuTime;
use heim::memory::Memory;
use heim::disk::Usage;
use std::collections::HashMap;

#[derive(Debug, Clone)]
pub struct SystemMetrics {
    cpu_usage: f64,
    memory_usage: Memory,
    disk_usage: HashMap<String, Usage>,
    network_stats: HashMap<String, NetworkStats>,
}

pub struct MetricsCollector {
    previous_cpu: Option<CpuTime>,
    metrics: Arc<RwLock<SystemMetrics>>,
    otel_meter: opentelemetry::metrics::Meter,
}

impl MetricsCollector {
    pub async fn new() -> anyhow::Result<Self> {
        let meter_provider = opentelemetry_otlp::new_pipeline()
            .metrics(opentelemetry_sdk::runtime::Tokio)
            .build()?;
            
        let meter = meter_provider.meter("system_metrics");

        Ok(Self {
            previous_cpu: None,
            metrics: Arc::new(RwLock::new(SystemMetrics::default())),
            otel_meter: meter,
        })
    }

    pub async fn collect_metrics(&mut self) -> anyhow::Result<()> {
        // CPU 使用率
        let cpu = heim::cpu::usage().await?;
        if let Some(prev_cpu) = self.previous_cpu.take() {
            let cpu_usage = self.calculate_cpu_usage(prev_cpu, cpu);
            self.record_cpu_usage(cpu_usage).await?;
        }
        self.previous_cpu = Some(cpu);

        // 内存使用情况
        let memory = heim::memory::memory().await?;
        self.record_memory_usage(&memory).await?;

        // 磁盘使用情况
        let mut disk_usage = HashMap::new();
        let partitions = heim::disk::partitions().await?;
        for partition in partitions {
            if let Ok(usage) = heim::disk::usage(partition.mount_point()).await {
                disk_usage.insert(
                    partition.mount_point().to_string_lossy().to_string(),
                    usage,
                );
            }
        }
        self.record_disk_usage(&disk_usage).await?;

        // 网络统计
        let network_stats = self.collect_network_stats().await?;
        self.record_network_stats(&network_stats).await?;

        // 更新指标
        let mut metrics = self.metrics.write().await;
        *metrics = SystemMetrics {
            cpu_usage,
            memory_usage: memory,
            disk_usage,
            network_stats,
        };

        Ok(())
    }

    async fn record_cpu_usage(&self, usage: f64) -> anyhow::Result<()> {
        let counter = self.otel_meter
            .f64_counter("cpu_usage")
            .with_description("CPU usage percentage")
            .init();
            
        counter.add(usage, &[]);
        Ok(())
    }

    async fn record_memory_usage(&self, memory: &Memory) -> anyhow::Result<()> {
        let gauge = self.otel_meter
            .f64_up_down_counter("memory_usage")
            .with_description("Memory usage in bytes")
            .init();
            
        gauge.add(memory.used().as_u64() as f64, &[]);
        Ok(())
    }

    async fn record_disk_usage(&self, usage: &HashMap<String, Usage>) -> anyhow::Result<()> {
        let gauge = self.otel_meter
            .f64_up_down_counter("disk_usage")
            .with_description("Disk usage in bytes")
            .init();
            
        for (path, usage) in usage {
            gauge.add(
                usage.used().as_u64() as f64,
                &[KeyValue::new("path", path.clone())],
            );
        }
        Ok(())
    }

    async fn record_network_stats(&self, stats: &HashMap<String, NetworkStats>) -> anyhow::Result<()> {
        let rx_counter = self.otel_meter
            .u64_counter("network_rx_bytes")
            .with_description("Network received bytes")
            .init();
            
        let tx_counter = self.otel_meter
            .u64_counter("network_tx_bytes")
            .with_description("Network transmitted bytes")
            .init();
            
        for (interface, stats) in stats {
            rx_counter.add(
                stats.received_bytes,
                &[KeyValue::new("interface", interface.clone())],
            );
            tx_counter.add(
                stats.transmitted_bytes,
                &[KeyValue::new("interface", interface.clone())],
            );
        }
        Ok(())
    }
}
```

## 3. 分布式追踪实现

```rust
use opentelemetry::trace::{Tracer, TracerProvider};
use opentelemetry::Context;

pub struct DistributedTracer {
    tracer: opentelemetry::trace::Tracer,
}

impl DistributedTracer {
    pub fn new() -> anyhow::Result<Self> {
        let tracer_provider = opentelemetry_otlp::new_pipeline()
            .tracing()
            .with_exporter(opentelemetry_otlp::new_exporter().tonic())
            .with_trace_config(
                opentelemetry_sdk::trace::config()
                    .with_sampler(opentelemetry_sdk::trace::Sampler::AlwaysOn)
                    .with_max_events_per_span(64)
                    .with_max_attributes_per_span(16)
            )
            .install_batch(opentelemetry_sdk::runtime::Tokio)?;

        let tracer = tracer_provider.tracer("metrics_monitor");

        Ok(Self { tracer })
    }

    pub async fn trace_operation<F, T>(&self, name: &str, f: F) -> anyhow::Result<T>
    where
        F: Future<Output = anyhow::Result<T>>,
    {
        let mut span = self.tracer
            .span_builder(name)
            .with_attributes(vec![
                KeyValue::new("service.name", "metrics_monitor"),
                KeyValue::new("operation", name),
            ])
            .start(&self.tracer);

        let cx = Context::current_with_span(span);
        let result = f.await;

        if let Err(ref e) = result {
            span.record_error(e);
            span.set_status(Status::Error {
                description: e.to_string().into(),
            });
        }

        span.end();
        result
    }
}
```

## 4. 指标控制器实现

```rust
pub struct MetricsController {
    collectors: Arc<DashMap<String, MetricsCollector>>,
    tracer: Arc<DistributedTracer>,
}

impl MetricsController {
    pub fn new(tracer: Arc<DistributedTracer>) -> Self {
        Self {
            collectors: Arc::new(DashMap::new()),
            tracer,
        }
    }

    pub async fn add_collector(&self, name: &str) -> anyhow::Result<()> {
        self.tracer.trace_operation("add_collector", async {
            let collector = MetricsCollector::new().await?;
            self.collectors.insert(name.to_string(), collector);
            Ok(())
        }).await
    }

    pub async fn remove_collector(&self, name: &str) -> anyhow::Result<()> {
        self.tracer.trace_operation("remove_collector", async {
            self.collectors.remove(name);
            Ok(())
        }).await
    }

    pub async fn start_collection(&self, interval: Duration) -> anyhow::Result<()> {
        let collectors = self.collectors.clone();
        let tracer = self.tracer.clone();

        tokio::spawn(async move {
            let mut interval = tokio::time::interval(interval);
            loop {
                interval.tick().await;
                for mut collector in collectors.iter_mut() {
                    if let Err(e) = tracer.trace_operation("collect_metrics", async {
                        collector.value_mut().collect_metrics().await
                    }).await {
                        tracing::error!("Error collecting metrics: {}", e);
                    }
                }
            }
        });

        Ok(())
    }

    pub async fn get_metrics(&self, name: &str) -> anyhow::Result<SystemMetrics> {
        self.tracer.trace_operation("get_metrics", async {
            let collector = self.collectors
                .get(name)
                .ok_or_else(|| anyhow::anyhow!("Collector not found"))?;
                
            Ok(collector.metrics.read().await.clone())
        }).await
    }
}
```

## 5. gRPC 服务实现

```rust
#[derive(Debug)]
pub struct MetricsService {
    controller: Arc<MetricsController>,
}

#[tonic::async_trait]
impl metrics_service_server::MetricsService for MetricsService {
    async fn get_metrics(
        &self,
        request: Request<GetMetricsRequest>,
    ) -> Result<Response<GetMetricsResponse>, Status> {
        let metrics = self.controller
            .get_metrics(&request.get_ref().collector_name)
            .await
            .map_err(|e| Status::internal(e.to_string()))?;

        Ok(Response::new(GetMetricsResponse {
            cpu_usage: metrics.cpu_usage,
            memory_used: metrics.memory_usage.used().as_u64(),
            memory_total: metrics.memory_usage.total().as_u64(),
            disk_usage: metrics.disk_usage
                .into_iter()
                .map(|(path, usage)| DiskUsage {
                    path,
                    used: usage.used().as_u64(),
                    total: usage.total().as_u64(),
                })
                .collect(),
            network_stats: metrics.network_stats
                .into_iter()
                .map(|(interface, stats)| NetworkStat {
                    interface,
                    rx_bytes: stats.received_bytes,
                    tx_bytes: stats.transmitted_bytes,
                })
                .collect(),
        }))
    }

    async fn control_collector(
        &self,
        request: Request<ControlCollectorRequest>,
    ) -> Result<Response<ControlCollectorResponse>, Status> {
        let req = request.get_ref();
        match req.action {
            CollectorAction::Start => {
                self.controller
                    .add_collector(&req.collector_name)
                    .await
                    .map_err(|e| Status::internal(e.to_string()))?;
            }
            CollectorAction::Stop => {
                self.controller
                    .remove_collector(&req.collector_name)
                    .await
                    .map_err(|e| Status::internal(e.to_string()))?;
            }
        }

        Ok(Response::new(ControlCollectorResponse {
            success: true,
            message: "Collector control successful".to_string(),
        }))
    }
}
```

## 6. 指标聚合器实现

```rust
pub struct MetricsAggregator {
    storage: Arc<MetricsStorage>,
    tracer: Arc<DistributedTracer>,
}

impl MetricsAggregator {
    pub fn new(storage: Arc<MetricsStorage>, tracer: Arc<DistributedTracer>) -> Self {
        Self { storage, tracer }
    }

    pub async fn aggregate_metrics(&self, time_range: TimeRange) -> anyhow::Result<AggregatedMetrics> {
        self.tracer.trace_operation("aggregate_metrics", async {
            let metrics = self.storage.get_metrics(time_range).await?;
            
            let cpu_stats = self.calculate_cpu_stats(&metrics);
            let memory_stats = self.calculate_memory_stats(&metrics);
            let disk_stats = self.calculate_disk_stats(&metrics);
            let network_stats = self.calculate_network_stats(&metrics);

            Ok(AggregatedMetrics {
                cpu_stats,
                memory_stats,
                disk_stats,
                network_stats,
                time_range,
            })
        }).await
    }

    async fn calculate_cpu_stats(&self, metrics: &[SystemMetrics]) -> CpuStats {
        let usage_values: Vec<f64> = metrics.iter()
            .map(|m| m.cpu_usage)
            .collect();

        CpuStats {
            min: usage_values.iter().fold(f64::INFINITY, |a, &b| a.min(b)),
            max: usage_values.iter().fold(f64::NEG_INFINITY, |a, &b| a.max(b)),
            avg: usage_values.iter().sum::<f64>() / usage_values.len() as f64,
        }
    }

    // Similar implementations for memory, disk, and network stats...
}
```

## 7. 告警系统实现

```rust
pub struct AlertSystem {
    rules: Arc<DashMap<String, AlertRule>>,
    notifier: Arc<AlertNotifier>,
    tracer: Arc<DistributedTracer>,
}

impl AlertSystem {
    pub fn new(notifier: Arc<AlertNotifier>, tracer: Arc<DistributedTracer>) -> Self {
        Self {
            rules: Arc::new(DashMap::new()),
            notifier,
            tracer,
        }
    }

    pub async fn add_rule(&self, rule: AlertRule) -> anyhow::Result<()> {
        self.tracer.trace_operation("add_alert_rule", async {
            self.rules.insert(rule.id.clone(), rule);
            Ok(())
        }).await
    }

    pub async fn check_metrics(&self, metrics: &SystemMetrics) -> anyhow::Result<()> {
        self.tracer.trace_operation("check_alerts", async {
            for rule in self.rules.iter() {
                if rule.should_alert(metrics) {
                    self.notifier.send_alert(Alert {
                        rule_id: rule.id.clone(),
                        message: rule.generate_message(metrics),
                        timestamp: chrono::Utc::now(),
                    }).await?;
                }
            }
            Ok(())
        }).await
    }
}

#[derive(Clone)]
pub struct AlertRule {
    id: String,
    condition: AlertCondition,
    threshold: f64,
    message_template: String,
}

impl AlertRule {
    fn should_alert(&self, metrics: &SystemMetrics) -> bool {
        match self.condition {
            AlertCondition::CpuUsageAbove => metrics.cpu_usage > self.threshold,
            AlertCondition::MemoryUsageAbove => {
                let usage = metrics.memory_usage.used().as_u64() as f64
                    / metrics.memory_usage.total().as_u64() as f64;
                usage > self.threshold
            }
            // Other conditions...
        }
    }
}
```

## 8. 存储系统实现

```rust
pub struct MetricsStorage {
    client: Client,
    tracer: Arc<DistributedTracer>,
}

impl MetricsStorage {
    pub async fn new(
        connection_string: &str,
        tracer: Arc<DistributedTracer>,
    ) -> anyhow::Result<Self> {
        let client = Client::connect(connection_string).await?;
        Ok(Self { client, tracer })
    }

    pub async fn store_metrics(&self, metrics: &SystemMetrics) -> anyhow::Result<()> {
        self.tracer.trace_operation("store_metrics", async {
            let document = self.serialize_metrics(metrics);
            self.client
                .database("metrics")
                .collection("system_metrics")
                .insert_one(document, None)
                .await?;
            Ok(())
        }).await
    }

    pub async fn get_metrics(&self, time_range: TimeRange) -> anyhow::Result<Vec<SystemMetrics>> {
        self.tracer.trace_operation("get_metrics", async {
            let filter = doc! {
                "timestamp": {
                    "$gte": time_range.start,
                    "$lte": time_range.end,
                }
            };

            let cursor = self.client
                .database("metrics")
                .collection("system_metrics")
                .find(filter, None)
                .await?;

            let metrics = cursor
                .try_collect::<Vec<Document>>()
                .await?
                .into_iter()
                .map(|doc| self.deserialize_metrics(&doc))
                .collect::<Result<Vec<_>, _>>()?;

            Ok(metrics)
        }).await
    }
}
```

## 9. 主程序实现

```rust
#[tokio::main]
async fn main() -> anyhow::Result<()> {
    // 初始化追踪器
    let tracer = Arc::new(DistributedTracer::new()?);

    // 初始化存储
    let storage = Arc::new(MetricsStorage::new(
        "mongodb://localhost:27017",
        tracer.clone(),
    ).await?);

    // 初始化告警系统
    let notifier = Arc::new(AlertNotifier::new());
    let alert_system = Arc::new(AlertSystem::new(notifier, tracer.clone()));

    // 初始化指标控制器
    let controller = Arc::new(MetricsController::new(tracer.clone()));

    // 初始化聚合器
    let aggregator = Arc::new(MetricsAggregator::new(storage.clone(), tracer.clone()));

    // 启动 gRPC 服务
    let addr = "[::1]:50051".parse()?;
    let metrics_service = MetricsService::new(controller.clone());

    println!("Starting metrics service on {}", addr);

    Server::builder()
        .add_service(MetricsServiceServer::new(metrics_service))
        .serve(addr)
        .await?;

    Ok(())
}
```

## 10. 配置文件示例

```yaml
collectors:
  system:
    enabled: true
    interval: 10s
    metrics:
      - cpu
      - memory
      - disk
      - network

alert_rules:
  - id: high_cpu_usage
    condition: cpu_usage_above
    threshold: 0.9
    message: "High CPU usage detected: {value}%"

  - id: low_memory
    condition: memory_usage_above
    threshold: 0.95
    message: "Low memory warning: {free_memory}MB remaining"

storage:
  type: mongodb
  url: mongodb://localhost:27017
  database: metrics
  retention_days: 30

tracing:
  service_name: metrics_monitor
  endpoint: http://localhost:4317
  sampling_ratio: 1.0

metrics:
  endpoint: http://localhost:4318
  export_interval: 15s
```

这个完整的示例展示了如何构建一个分布式监控系统，包括：

1. 系统指标收集
2. 分布式追踪
3. 指标控制
4. 指标聚合
5. 告警系统
6. 存储系统
7. gRPC 服务

主要特性：

- 异步处理
- 分布式追踪
- 指标收集
- 告警机制
- 数据存储
- 指标聚合
- 配置管理
- 错误处理
- 可扩展性

这个实现提供了完整的监控解决方案，可以根据需要进行扩展和定制。
