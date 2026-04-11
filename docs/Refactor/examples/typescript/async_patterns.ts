/**
 * TypeScript 异步编程模式示例
 * 
 * 本文件演示现代异步编程：
 * - Promise模式
 * - Async/Await
 * - 异步迭代器
 * - 并发控制
 */

// ============================================
// 1. Promise 高级模式
// ============================================

// Promise 工具函数
const PromiseUtils = {
    // 延迟指定时间
    delay: <T>(ms: number, value?: T): Promise<T> => 
        new Promise(resolve => setTimeout(() => resolve(value!), ms)),
    
    // 带超时的Promise
    withTimeout: <T>(promise: Promise<T>, ms: number, errorMessage?: string): Promise<T> => {
        const timeout = new Promise<never>((_, reject) => 
            setTimeout(() => reject(new Error(errorMessage || `Timeout after ${ms}ms`)), ms)
        );
        return Promise.race([promise, timeout]);
    },
    
    // 重试机制
    retry: async <T>(
        fn: () => Promise<T>, 
        maxAttempts: number = 3, 
        delay: number = 1000
    ): Promise<T> => {
        let lastError: Error;
        
        for (let i = 0; i < maxAttempts; i++) {
            try {
                return await fn();
            } catch (error) {
                lastError = error as Error;
                if (i < maxAttempts - 1) {
                    await PromiseUtils.delay(delay * Math.pow(2, i));  // 指数退避
                }
            }
        }
        
        throw lastError!;
    },
    
    // 按顺序执行Promise
    sequence: <T>(promises: (() => Promise<T>)[]): Promise<T[]> => 
        promises.reduce(
            (acc, fn) => acc.then(results => fn().then(r => [...results, r])),
            Promise.resolve([] as T[])
        ),
    
    // 带并发限制的Promise.all
    allSettledWithConcurrency: async <T>(
        tasks: (() => Promise<T>)[], 
        concurrency: number
    ): Promise<PromiseSettledResult<T>[]> => {
        const results: PromiseSettledResult<T>[] = [];
        const executing: Promise<void>[] = [];
        
        for (let i = 0; i < tasks.length; i++) {
            const task = tasks[i];
            const promise = task().then(
                value => { results[i] = { status: 'fulfilled', value }; },
                reason => { results[i] = { status: 'rejected', reason }; }
            ).then(() => {});
            
            results.push(undefined as any);
            executing.push(promise);
            
            if (executing.length >= concurrency) {
                await Promise.race(executing);
                executing.splice(executing.findIndex(p => p === promise), 1);
            }
        }
        
        await Promise.all(executing);
        return results;
    }
};

// 演示Promise工具
async function demonstratePromiseUtils() {
    console.log("=== Promise 工具演示 ===");
    
    // delay
    console.log("等待1秒...");
    await PromiseUtils.delay(1000);
    console.log("等待完成");
    
    // withTimeout - 成功情况
    const fastOperation = Promise.resolve("快速完成");
    const result1 = await PromiseUtils.withTimeout(fastOperation, 5000);
    console.log("超时包装（成功）:", result1);
    
    // withTimeout - 超时情况
    try {
        const slowOperation = PromiseUtils.delay(2000, "太慢了");
        await PromiseUtils.withTimeout(slowOperation, 100, "操作超时");
    } catch (error) {
        console.log("超时错误:", (error as Error).message);
    }
    
    // retry
    let attempts = 0;
    const unreliable = async () => {
        attempts++;
        if (attempts < 3) {
            throw new Error(`尝试 ${attempts} 失败`);
        }
        return `成功于尝试 ${attempts}`;
    };
    
    const retryResult = await PromiseUtils.retry(unreliable, 5, 100);
    console.log("重试结果:", retryResult);
    
    // sequence
    const delayedLogs = [
        () => PromiseUtils.delay(100, "第一个").then(v => { console.log(v); return v; }),
        () => PromiseUtils.delay(50, "第二个").then(v => { console.log(v); return v; }),
        () => PromiseUtils.delay(150, "第三个").then(v => { console.log(v); return v; })
    ];
    
    console.log("按顺序执行:");
    await PromiseUtils.sequence(delayedLogs);
}

// ============================================
// 2. Async/Await 模式
// ============================================

// 异步生成器
async function* asyncRange(start: number, end: number, delay: number = 100): AsyncGenerator<number> {
    for (let i = start; i < end; i++) {
        await PromiseUtils.delay(delay);
        yield i;
    }
}

// 异步迭代处理
async function processAsyncIterable<T, U>(
    iterable: AsyncIterable<T>,
    processor: (item: T) => Promise<U>,
    concurrency: number = 1
): Promise<U[]> {
    const results: U[] = [];
    const iterator = iterable[Symbol.asyncIterator]();
    
    if (concurrency === 1) {
        // 顺序处理
        for await (const item of iterable) {
            results.push(await processor(item));
        }
    } else {
        // 并发处理
        const executing: Promise<void>[] = [];
        let index = 0;
        
        while (true) {
            const { value, done } = await iterator.next();
            if (done) break;
            
            const currentIndex = index++;
            const promise = processor(value).then(result => {
                results[currentIndex] = result;
            });
            
            executing.push(promise);
            
            if (executing.length >= concurrency) {
                await Promise.race(executing);
            }
        }
        
        await Promise.all(executing);
    }
    
    return results;
}

// 演示Async/Await模式
async function demonstrateAsyncAwait() {
    console.log("\n=== Async/Await 模式演示 ===");
    
    // 异步生成器
    console.log("异步生成器 (1-5, 100ms延迟):");
    for await (const num of asyncRange(1, 6)) {
        process.stdout.write(`${num} `);
    }
    console.log();
    
    // 异步迭代处理
    async function* dataGenerator() {
        const items = ['A', 'B', 'C', 'D', 'E'];
        for (const item of items) {
            await PromiseUtils.delay(50);
            yield item;
        }
    }
    
    const processor = async (item: string) => {
        await PromiseUtils.delay(100);
        return item.toLowerCase();
    };
    
    console.log("\n顺序处理:");
    const sequential = await processAsyncIterable(dataGenerator(), processor, 1);
    console.log("结果:", sequential);
    
    console.log("\n并发处理 (2并发):");
    const concurrent = await processAsyncIterable(dataGenerator(), processor, 2);
    console.log("结果:", concurrent);
}

// ============================================
// 3. 异步迭代器
// ============================================

// 自定义异步可迭代对象
class AsyncQueue<T> implements AsyncIterable<T> {
    private queue: T[] = [];
    private resolvers: Array<(value: IteratorResult<T>) => void> = [];
    private closed = false;
    
    enqueue(item: T): void {
        if (this.closed) return;
        
        if (this.resolvers.length > 0) {
            const resolve = this.resolvers.shift()!;
            resolve({ value: item, done: false });
        } else {
            this.queue.push(item);
        }
    }
    
    close(): void {
        this.closed = true;
        while (this.resolvers.length > 0) {
            const resolve = this.resolvers.shift()!;
            resolve({ value: undefined as any, done: true });
        }
    }
    
    [Symbol.asyncIterator](): AsyncIterator<T> {
        return {
            next: (): Promise<IteratorResult<T>> => {
                if (this.queue.length > 0) {
                    return Promise.resolve({
                        value: this.queue.shift()!,
                        done: false
                    });
                }
                
                if (this.closed) {
                    return Promise.resolve({
                        value: undefined as any,
                        done: true
                    });
                }
                
                return new Promise(resolve => {
                    this.resolvers.push(resolve);
                });
            }
        };
    }
}

// 分页数据获取器
interface PaginatedResult<T> {
    items: T[];
    hasMore: boolean;
    nextCursor?: string;
}

async function* paginatedFetcher<T>(
    fetchPage: (cursor?: string) => Promise<PaginatedResult<T>>
): AsyncGenerator<T[]> {
    let cursor: string | undefined;
    
    do {
        const result = await fetchPage(cursor);
        yield result.items;
        cursor = result.nextCursor;
    } while (cursor);
}

// 演示异步迭代器
async function demonstrateAsyncIterators() {
    console.log("\n=== 异步迭代器演示 ===");
    
    // 异步队列
    const queue = new AsyncQueue<string>();
    
    // 生产者
    setTimeout(() => {
        queue.enqueue("消息1");
        queue.enqueue("消息2");
    }, 100);
    
    setTimeout(() => {
        queue.enqueue("消息3");
        queue.close();
    }, 300);
    
    console.log("从队列消费:");
    for await (const msg of queue) {
        console.log("  收到:", msg);
    }
    console.log("队列已关闭");
    
    // 分页获取
    let pageCount = 0;
    const mockFetch = async (cursor?: string): Promise<PaginatedResult<number>> => {
        pageCount++;
        const start = cursor ? parseInt(cursor) : 0;
        const items = [start, start + 1, start + 2];
        
        return {
            items,
            hasMore: pageCount < 3,
            nextCursor: pageCount < 3 ? String(start + 3) : undefined
        };
    };
    
    console.log("\n分页获取数据:");
    for await (const page of paginatedFetcher(mockFetch)) {
        console.log("  页面数据:", page);
    }
}

// ============================================
// 4. 并发控制
// ============================================

// 信号量（Semaphore）
class Semaphore {
    private permits: number;
    private waiting: Array<() => void> = [];
    
    constructor(permits: number) {
        this.permits = permits;
    }
    
    async acquire(): Promise<void> {
        if (this.permits > 0) {
            this.permits--;
            return;
        }
        
        return new Promise(resolve => {
            this.waiting.push(resolve);
        });
    }
    
    release(): void {
        if (this.waiting.length > 0) {
            const next = this.waiting.shift()!;
            next();
        } else {
            this.permits++;
        }
    }
    
    async runWithPermit<T>(fn: () => Promise<T>): Promise<T> {
        await this.acquire();
        try {
            return await fn();
        } finally {
            this.release();
        }
    }
}

// 任务队列（带优先级）
interface Task<T> {
    id: string;
    priority: number;
    execute: () => Promise<T>;
    resolve: (value: T) => void;
    reject: (error: Error) => void;
}

class PriorityTaskQueue<T> {
    private queue: Task<T>[] = [];
    private running = 0;
    
    constructor(private concurrency: number) {}
    
    add(execute: () => Promise<T>, priority: number = 0, id: string = `task-${Date.now()}`): Promise<T> {
        return new Promise((resolve, reject) => {
            const task: Task<T> = { id, priority, execute, resolve, reject };
            
            // 按优先级插入
            const index = this.queue.findIndex(t => t.priority < priority);
            if (index === -1) {
                this.queue.push(task);
            } else {
                this.queue.splice(index, 0, task);
            }
            
            this.process();
        });
    }
    
    private async process(): Promise<void> {
        if (this.running >= this.concurrency || this.queue.length === 0) {
            return;
        }
        
        const task = this.queue.shift()!;
        this.running++;
        
        try {
            const result = await task.execute();
            task.resolve(result);
        } catch (error) {
            task.reject(error as Error);
        } finally {
            this.running--;
            this.process();
        }
    }
}

// 批量处理器
class BatchProcessor<T, R> {
    private batch: T[] = [];
    private timeoutId: ReturnType<typeof setTimeout> | null = null;
    
    constructor(
        private processBatch: (items: T[]) => Promise<R[]>,
        private maxBatchSize: number = 100,
        private maxWaitMs: number = 50
    ) {}
    
    async add(item: T): Promise<R> {
        return new Promise((resolve, reject) => {
            this.batch.push(item);
            
            if (this.batch.length >= this.maxBatchSize) {
                this.flush();
            } else if (!this.timeoutId) {
                this.timeoutId = setTimeout(() => this.flush(), this.maxWaitMs);
            }
            
            // 这里简化处理，实际应该存储resolve/reject回调
            setTimeout(async () => {
                try {
                    const results = await this.processBatch([item]);
                    resolve(results[0]);
                } catch (error) {
                    reject(error);
                }
            }, this.maxWaitMs + 10);
        });
    }
    
    private async flush(): Promise<void> {
        if (this.batch.length === 0) return;
        
        if (this.timeoutId) {
            clearTimeout(this.timeoutId);
            this.timeoutId = null;
        }
        
        const currentBatch = [...this.batch];
        this.batch = [];
        
        await this.processBatch(currentBatch);
    }
}

// 演示并发控制
async function demonstrateConcurrencyControl() {
    console.log("\n=== 并发控制演示 ===");
    
    // 信号量
    const semaphore = new Semaphore(2);
    const results: string[] = [];
    
    const tasks = [1, 2, 3, 4, 5].map(async (n) => {
        await semaphore.acquire();
        try {
            const start = Date.now();
            await PromiseUtils.delay(100);
            const duration = Date.now() - start;
            results.push(`任务${n} 完成 (${duration}ms)`);
        } finally {
            semaphore.release();
        }
    });
    
    await Promise.all(tasks);
    console.log("信号量结果 (最大2并发):");
    results.forEach(r => console.log("  " + r));
    
    // 优先级队列
    console.log("\n优先级队列 (2并发):");
    const priorityQueue = new PriorityTaskQueue<string>(2);
    
    const logWithTime = (msg: string) => {
        console.log(`  [${new Date().toISOString().slice(11, 19)}] ${msg}`);
    };
    
    const p1 = priorityQueue.add(async () => {
        logWithTime("低优先级任务开始");
        await PromiseUtils.delay(200);
        logWithTime("低优先级任务完成");
        return "低优先级";
    }, 1, "low");
    
    const p2 = priorityQueue.add(async () => {
        logWithTime("高优先级任务开始");
        await PromiseUtils.delay(100);
        logWithTime("高优先级任务完成");
        return "高优先级";
    }, 10, "high");
    
    const p3 = priorityQueue.add(async () => {
        logWithTime("中优先级任务开始");
        await PromiseUtils.delay(150);
        logWithTime("中优先级任务完成");
        return "中优先级";
    }, 5, "medium");
    
    await Promise.all([p1, p2, p3]);
}

// ============================================
// 5. 取消模式
// ============================================

// 可取消的Promise
interface CancellablePromise<T> extends Promise<T> {
    cancel: () => void;
}

function makeCancellable<T>(promise: Promise<T>): CancellablePromise<T> {
    let isCancelled = false;
    let cancelFn: () => void = () => {};
    
    const wrappedPromise = new Promise<T>((resolve, reject) => {
        cancelFn = () => {
            isCancelled = true;
            reject(new Error('Cancelled'));
        };
        
        promise.then(
            value => {
                if (!isCancelled) resolve(value);
            },
            error => {
                if (!isCancelled) reject(error);
            }
        );
    }) as CancellablePromise<T>;
    
    wrappedPromise.cancel = cancelFn;
    return wrappedPromise;
}

// AbortController 模式
async function fetchWithAbort(url: string, signal: AbortSignal): Promise<Response> {
    return fetch(url, { signal });
}

// 演示取消模式
async function demonstrateCancellation() {
    console.log("\n=== 取消模式演示 ===");
    
    // 可取消Promise
    const slowTask = makeCancellable(PromiseUtils.delay(2000, "完成"));
    
    setTimeout(() => {
        console.log("取消慢任务");
        slowTask.cancel();
    }, 500);
    
    try {
        await slowTask;
    } catch (error) {
        console.log("任务被取消:", (error as Error).message);
    }
    
    // AbortController
    const controller = new AbortController();
    
    setTimeout(() => {
        console.log("中止请求");
        controller.abort();
    }, 100);
    
    try {
        // 使用示例URL（实际可能失败，仅演示）
        await fetchWithAbort('https://httpbin.org/delay/5', controller.signal);
    } catch (error) {
        if ((error as Error).name === 'AbortError') {
            console.log("请求被中止");
        } else {
            console.log("其他错误:", (error as Error).message);
        }
    }
}

// ============================================
// 主函数
// ============================================

async function main() {
    console.log("========================================");
    console.log("TypeScript 异步编程模式示例");
    console.log("========================================");
    
    await demonstratePromiseUtils();
    await demonstrateAsyncAwait();
    await demonstrateAsyncIterators();
    await demonstrateConcurrencyControl();
    await demonstrateCancellation();
    
    console.log("\n========================================");
    console.log("所有异步模式演示完成");
    console.log("========================================");
}

main().catch(console.error);
