import java.util.*;
import java.util.concurrent.*;
import java.util.concurrent.atomic.*;
import java.util.stream.*;

/**
 * Java 并发集合示例
 * 
 * 本文件演示Java中的线程安全集合：
 * - ConcurrentHashMap
 * - CopyOnWriteArrayList
 * - BlockingQueue
 * - ConcurrentSkipListMap
 */
public class ConcurrentCollections {

    // ============================================
    // 1. ConcurrentHashMap演示
    // ============================================
    
    static void demonstrateConcurrentHashMap() {
        System.out.println("=== ConcurrentHashMap演示 ===");
        
        ConcurrentHashMap<String, Integer> map = new ConcurrentHashMap<>();
        
        // 基本操作
        map.put("key1", 100);
        map.putIfAbsent("key1", 200);  // 不会替换
        map.putIfAbsent("key2", 300);
        System.out.println("初始状态: " + map);
        
        // 原子性更新
        map.compute("key1", (k, v) -> v == null ? 1 : v * 2);
        System.out.println("compute后: " + map);
        
        map.computeIfAbsent("key3", k -> k.length() * 10);
        System.out.println("computeIfAbsent后: " + map);
        
        map.computeIfPresent("key1", (k, v) -> v + 1);
        System.out.println("computeIfPresent后: " + map);
        
        // 合并操作
        map.merge("key1", 50, Integer::sum);
        map.merge("key4", 50, Integer::sum);
        System.out.println("merge后: " + map);
        
        // 批量操作
        System.out.println("\n批量操作:");
        map.forEach(3, (k, v) -> System.out.println(k + " -> " + v));
        
        // 搜索
        String result = map.search(3, (k, v) -> v > 100 ? k : null);
        System.out.println("第一个值>100的键: " + result);
        
        // 归约
        long sum = map.reduceValuesToLong(3, v -> v, 0, Long::sum);
        System.out.println("所有值的总和: " + sum);
        
        // 并行计算（使用ForkJoinPool）
        ConcurrentHashMap<String, Long> wordCounts = new ConcurrentHashMap<>();
        String[] words = {"apple", "banana", "apple", "cherry", "banana", "apple"};
        
        for (String word : words) {
            wordCounts.merge(word, 1L, Long::sum);
        }
        System.out.println("词频统计: " + wordCounts);
    }

    // ============================================
    // 2. CopyOnWriteArrayList演示
    // ============================================
    
    static void demonstrateCopyOnWriteArrayList() {
        System.out.println("\n=== CopyOnWriteArrayList演示 ===");
        
        // 适合读多写少的场景
        CopyOnWriteArrayList<String> list = new CopyOnWriteArrayList<>();
        
        // 添加元素
        list.add("Item 1");
        list.add("Item 2");
        list.add("Item 3");
        System.out.println("初始列表: " + list);
        
        // 迭代器不会抛出ConcurrentModificationException
        System.out.println("\n遍历列表:");
        for (String item : list) {
            System.out.println("  读取: " + item);
            // 可以在遍历时修改（会创建新副本）
            if (item.equals("Item 2")) {
                list.add("Item 4");  // 不会在当前迭代中显示
            }
        }
        System.out.println("修改后列表: " + list);
        
        // 并发读写演示
        CopyOnWriteArrayList<Integer> numbers = new CopyOnWriteArrayList<>();
        ExecutorService executor = Executors.newFixedThreadPool(3);
        CountDownLatch latch = new CountDownLatch(3);
        
        // 写入线程
        executor.submit(() -> {
            for (int i = 0; i < 5; i++) {
                numbers.add(i);
                System.out.println("写入: " + i);
                sleep(50);
            }
            latch.countDown();
        });
        
        // 两个读取线程
        for (int i = 0; i < 2; i++) {
            final int readerId = i;
            executor.submit(() -> {
                for (int j = 0; j < 3; j++) {
                    System.out.println("读者" + readerId + " 看到: " + numbers);
                    sleep(80);
                }
                latch.countDown();
            });
        }
        
        try {
            latch.await();
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
        }
        executor.shutdown();
        
        System.out.println("最终结果: " + numbers);
    }

    // ============================================
    // 3. BlockingQueue演示
    // ============================================
    
    static void demonstrateBlockingQueue() {
        System.out.println("\n=== BlockingQueue演示 ===");
        
        // ArrayBlockingQueue: 有界队列，FIFO
        BlockingQueue<String> arrayQueue = new ArrayBlockingQueue<>(3);
        
        // LinkedBlockingQueue: 可选有界，通常用于生产者-消费者
        BlockingQueue<Integer> linkedQueue = new LinkedBlockingQueue<>(10);
        
        // PriorityBlockingQueue: 优先级队列
        BlockingQueue<Integer> priorityQueue = new PriorityBlockingQueue<>();
        
        // 生产者-消费者演示
        demonstrateProducerConsumer(linkedQueue);
        
        // 优先级队列演示
        System.out.println("\n优先级队列演示:");
        Random random = new Random();
        for (int i = 0; i < 10; i++) {
            int priority = random.nextInt(100);
            priorityQueue.offer(priority);
            System.out.print(priority + " ");
        }
        System.out.println();
        
        System.out.println("按优先级取出:");
        while (!priorityQueue.isEmpty()) {
            System.out.print(priorityQueue.poll() + " ");
        }
        System.out.println();
    }
    
    static void demonstrateProducerConsumer(BlockingQueue<Integer> queue) {
        System.out.println("\n生产者-消费者模式:");
        
        ExecutorService executor = Executors.newFixedThreadPool(3);
        CountDownLatch latch = new CountDownLatch(3);
        
        // 两个生产者
        for (int p = 0; p < 2; p++) {
            final int producerId = p;
            executor.submit(() -> {
                try {
                    for (int i = 0; i < 5; i++) {
                        int value = producerId * 100 + i;
                        queue.put(value);  // 阻塞直到有空间
                        System.out.println("生产者" + producerId + " 生产: " + value 
                                         + " (队列大小: " + queue.size() + ")");
                        sleep(50);
                    }
                } catch (InterruptedException e) {
                    Thread.currentThread().interrupt();
                }
                latch.countDown();
            });
        }
        
        // 一个消费者
        executor.submit(() -> {
            try {
                for (int i = 0; i < 10; i++) {
                    Integer value = queue.take();  // 阻塞直到有元素
                    System.out.println("消费者 消费: " + value 
                                     + " (队列大小: " + queue.size() + ")");
                    sleep(80);
                }
            } catch (InterruptedException e) {
                Thread.currentThread().interrupt();
            }
            latch.countDown();
        });
        
        try {
            latch.await();
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
        }
        executor.shutdown();
    }

    // ============================================
    // 4. ConcurrentSkipListMap演示
    // ============================================
    
    static void demonstrateConcurrentSkipListMap() {
        System.out.println("\n=== ConcurrentSkipListMap演示 ===");
        
        // 线程安全的有序Map
        ConcurrentSkipListMap<Integer, String> map = new ConcurrentSkipListMap<>();
        
        // 添加元素
        map.put(3, "Three");
        map.put(1, "One");
        map.put(5, "Five");
        map.put(2, "Two");
        map.put(4, "Four");
        
        System.out.println("有序Map: " + map);
        
        // 范围操作
        System.out.println("\n范围操作:");
        System.out.println("头元素: " + map.firstEntry());
        System.out.println("尾元素: " + map.lastEntry());
        System.out.println("2到4之间的元素: " + map.subMap(2, true, 4, true));
        System.out.println("小于3的元素: " + map.headMap(3));
        System.out.println("大于等于3的元素: " + map.tailMap(3));
        
        // 原子性替换
        map.replace(3, "Three", "THREE");
        System.out.println("\n替换后: " + map);
        
        // 并发修改时遍历（不会抛出异常）
        System.out.println("\n遍历时修改:");
        for (Map.Entry<Integer, String> entry : map.entrySet()) {
            System.out.println("  " + entry.getKey() + " -> " + entry.getValue());
            if (entry.getKey() == 2) {
                map.put(6, "Six");  // 安全地修改
            }
        }
        System.out.println("修改后: " + map);
    }

    // ============================================
    // 5. 其他并发集合
    // ============================================
    
    static void demonstrateOtherCollections() {
        System.out.println("\n=== 其他并发集合演示 ===");
        
        // ConcurrentLinkedQueue: 无锁队列
        ConcurrentLinkedQueue<String> clq = new ConcurrentLinkedQueue<>();
        clq.offer("A");
        clq.offer("B");
        clq.offer("C");
        System.out.println("ConcurrentLinkedQueue: " + clq);
        System.out.println("出队: " + clq.poll());
        System.out.println("剩余: " + clq);
        
        // ConcurrentLinkedDeque: 双端队列
        ConcurrentLinkedDeque<Integer> cld = new ConcurrentLinkedDeque<>();
        cld.addFirst(1);
        cld.addLast(2);
        cld.addFirst(0);
        System.out.println("\nConcurrentLinkedDeque: " + cld);
        System.out.println("移除首尾: " + cld.removeFirst() + ", " + cld.removeLast());
        
        // CopyOnWriteArraySet: 基于CopyOnWriteArrayList的Set
        CopyOnWriteArraySet<String> cows = new CopyOnWriteArraySet<>();
        cows.add("X");
        cows.add("Y");
        cows.add("X");  // 重复，不会添加
        System.out.println("\nCopyOnWriteArraySet: " + cows);
    }

    // ============================================
    // 6. 性能对比演示
    // ============================================
    
    static void demonstratePerformanceComparison() {
        System.out.println("\n=== 性能对比演示 ===");
        
        final int THREADS = 4;
        final int OPERATIONS = 100000;
        
        // 非线程安全 + synchronized
        Map<String, Integer> syncMap = Collections.synchronizedMap(new HashMap<>());
        
        // 线程安全
        ConcurrentHashMap<String, Integer> concurrentMap = new ConcurrentHashMap<>();
        
        // 测试synchronizedMap
        long syncTime = benchmarkMap(syncMap, THREADS, OPERATIONS);
        System.out.printf("SynchronizedMap: %d ms%n", syncTime);
        
        // 测试ConcurrentHashMap
        long concurrentTime = benchmarkMap(concurrentMap, THREADS, OPERATIONS);
        System.out.printf("ConcurrentHashMap: %d ms%n", concurrentTime);
        
        System.out.printf("性能提升: %.2fx%n", (double) syncTime / concurrentTime);
    }
    
    static long benchmarkMap(Map<String, Integer> map, int threads, int operations) {
        ExecutorService executor = Executors.newFixedThreadPool(threads);
        CountDownLatch latch = new CountDownLatch(threads);
        
        long start = System.currentTimeMillis();
        
        for (int t = 0; t < threads; t++) {
            final int threadId = t;
            executor.submit(() -> {
                for (int i = 0; i < operations / threads; i++) {
                    String key = "key" + (threadId * 10000 + i);
                    map.put(key, i);
                    map.get(key);
                }
                latch.countDown();
            });
        }
        
        try {
            latch.await();
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
        }
        
        executor.shutdown();
        return System.currentTimeMillis() - start;
    }

    // ============================================
    // 辅助方法
    // ============================================
    
    static void sleep(long millis) {
        try {
            Thread.sleep(millis);
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
        }
    }

    // ============================================
    // 主函数
    // ============================================
    
    public static void main(String[] args) {
        System.out.println("========================================");
        System.out.println("Java 并发集合示例");
        System.out.println("========================================");
        
        demonstrateConcurrentHashMap();
        demonstrateCopyOnWriteArrayList();
        demonstrateBlockingQueue();
        demonstrateConcurrentSkipListMap();
        demonstrateOtherCollections();
        demonstratePerformanceComparison();
        
        System.out.println("\n========================================");
        System.out.println("所有并发集合演示完成");
        System.out.println("========================================");
    }
}
