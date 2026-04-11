import java.util.*;
import java.util.function.*;
import java.util.stream.*;

/**
 * Java 函数式编程模式示例
 * 
 * 本文件演示现代Java中的函数式编程：
 * - Lambda表达式和函数式接口
 * - Stream API使用
 * - Optional处理
 * - 方法引用
 */
public class FunctionalPatterns {

    // ============================================
    // 1. 函数式接口定义
    // ============================================
    
    @FunctionalInterface
    interface Calculator {
        int operate(int a, int b);
        
        // 默认方法
        default int multiply(int a, int b) {
            return a * b;
        }
        
        // 静态方法
        static int power(int base, int exp) {
            return (int) Math.pow(base, exp);
        }
    }
    
    @FunctionalInterface
    interface Validator<T> {
        boolean validate(T value);
        
        // 默认方法：与另一个验证器组合
        default Validator<T> and(Validator<T> other) {
            return value -> this.validate(value) && other.validate(value);
        }
        
        default Validator<T> or(Validator<T> other) {
            return value -> this.validate(value) || other.validate(value);
        }
        
        default Validator<T> negate() {
            return value -> !this.validate(value);
        }
    }

    // ============================================
    // 2. Lambda表达式演示
    // ============================================
    
    static void demonstrateLambdas() {
        System.out.println("=== Lambda表达式演示 ===");
        
        // 使用自定义函数式接口
        Calculator add = (a, b) -> a + b;
        Calculator subtract = (a, b) -> a - b;
        
        System.out.println("10 + 5 = " + add.operate(10, 5));
        System.out.println("10 - 5 = " + subtract.operate(10, 5));
        System.out.println("10 * 5 = " + add.multiply(10, 5));
        System.out.println("2^3 = " + Calculator.power(2, 3));
        
        // 使用标准函数式接口
        // Predicate<T>: T -> boolean
        Predicate<Integer> isEven = n -> n % 2 == 0;
        System.out.println("4 是偶数: " + isEven.test(4));
        
        // Function<T, R>: T -> R
        Function<String, Integer> length = String::length;
        System.out.println("'Hello' 长度: " + length.apply("Hello"));
        
        // Consumer<T>: T -> void
        Consumer<String> printer = System.out::println;
        printer.accept("使用Consumer输出");
        
        // Supplier<T>: () -> T
        Supplier<Double> random = Math::random;
        System.out.println("随机数: " + random.get());
        
        // BiFunction<T, U, R>: (T, U) -> R
        BiFunction<String, String, String> concat = String::concat;
        System.out.println(concat.apply("Hello, ", "World!"));
    }

    // ============================================
    // 3. Stream API演示
    // ============================================
    
    static void demonstrateStreams() {
        System.out.println("\n=== Stream API演示 ===");
        
        List<Integer> numbers = Arrays.asList(1, 2, 3, 4, 5, 6, 7, 8, 9, 10);
        
        // 基本操作：过滤、映射、收集
        List<Integer> evenSquares = numbers.stream()
            .filter(n -> n % 2 == 0)           // 过滤偶数
            .map(n -> n * n)                   // 映射为平方
            .collect(Collectors.toList());     // 收集到列表
        System.out.println("偶数的平方: " + evenSquares);
        
        // 归约操作
        int sum = numbers.stream()
            .reduce(0, Integer::sum);
        System.out.println("总和: " + sum);
        
        // 分组
        Map<String, List<Integer>> groups = numbers.stream()
            .collect(Collectors.groupingBy(n -> n % 2 == 0 ? "偶数" : "奇数"));
        System.out.println("分组结果: " + groups);
        
        // 分区
        Map<Boolean, List<Integer>> partitioned = numbers.stream()
            .collect(Collectors.partitioningBy(n -> n > 5));
        System.out.println("分区结果 (>5): " + partitioned);
        
        // 统计
        IntSummaryStatistics stats = numbers.stream()
            .mapToInt(Integer::intValue)
            .summaryStatistics();
        System.out.println("统计: " + stats);
        
        // 并行流（大数据集时使用）
        long parallelSum = numbers.parallelStream()
            .mapToLong(n -> n)
            .sum();
        System.out.println("并行流求和: " + parallelSum);
    }

    // ============================================
    // 4. 复杂Stream操作
    // ============================================
    
    static class Person {
        private final String name;
        private final int age;
        private final String department;
        private final double salary;
        
        Person(String name, int age, String department, double salary) {
            this.name = name;
            this.age = age;
            this.department = department;
            this.salary = salary;
        }
        
        String getName() { return name; }
        int getAge() { return age; }
        String getDepartment() { return department; }
        double getSalary() { return salary; }
        
        @Override
        public String toString() {
            return String.format("%s(%d, %s, %.0f)", name, age, department, salary);
        }
    }
    
    static void demonstrateAdvancedStreams() {
        System.out.println("\n=== 高级Stream操作 ===");
        
        List<Person> people = Arrays.asList(
            new Person("Alice", 30, "Engineering", 80000),
            new Person("Bob", 25, "Sales", 60000),
            new Person("Charlie", 35, "Engineering", 90000),
            new Person("Diana", 28, "Marketing", 70000),
            new Person("Eve", 32, "Sales", 75000)
        );
        
        // 按部门分组并计算平均工资
        Map<String, Double> avgSalaryByDept = people.stream()
            .collect(Collectors.groupingBy(
                Person::getDepartment,
                Collectors.averagingDouble(Person::getSalary)
            ));
        System.out.println("部门平均工资: " + avgSalaryByDept);
        
        // 找出每个部门工资最高的人
        Map<String, Optional<Person>> topEarnersByDept = people.stream()
            .collect(Collectors.groupingBy(
                Person::getDepartment,
                Collectors.maxBy(Comparator.comparingDouble(Person::getSalary))
            ));
        System.out.println("部门最高工资: " + topEarnersByDept);
        
        // 多级分组
        Map<String, Map<String, List<Person>>> byDeptAndAgeGroup = people.stream()
            .collect(Collectors.groupingBy(
                Person::getDepartment,
                Collectors.groupingBy(p -> p.getAge() >= 30 ? "Senior" : "Junior")
            ));
        System.out.println("部门-年龄分组: " + byDeptAndAgeGroup);
        
        // 连接字符串
        String names = people.stream()
            .map(Person::getName)
            .collect(Collectors.joining(", ", "[", "]"));
        System.out.println("所有人名: " + names);
        
        // 自定义收集器：计算方差
        double meanSalary = people.stream()
            .mapToDouble(Person::getSalary)
            .average()
            .orElse(0);
        double variance = people.stream()
            .mapToDouble(p -> Math.pow(p.getSalary() - meanSalary, 2))
            .average()
            .orElse(0);
        System.out.printf("工资方差: %.2f%n", variance);
    }

    // ============================================
    // 5. Optional处理
    // ============================================
    
    static void demonstrateOptional() {
        System.out.println("\n=== Optional演示 ===");
        
        // 创建Optional
        Optional<String> present = Optional.of("Hello");
        Optional<String> empty = Optional.empty();
        Optional<String> nullable = Optional.ofNullable(getNullableValue());
        
        // 检查是否存在
        System.out.println("present.isPresent(): " + present.isPresent());
        System.out.println("empty.isEmpty(): " + empty.isEmpty());
        
        // 安全获取值
        String value1 = present.orElse("默认值");
        String value2 = empty.orElse("默认值");
        System.out.println("present orElse: " + value1);
        System.out.println("empty orElse: " + value2);
        
        // 延迟计算默认值
        String value3 = empty.orElseGet(() -> "延迟计算的默认值");
        System.out.println("orElseGet: " + value3);
        
        // 转换值
        Optional<Integer> length = present.map(String::length);
        System.out.println("字符串长度: " + length.orElse(0));
        
        // 链式操作
        Optional<String> result = present
            .filter(s -> s.length() > 3)
            .map(String::toUpperCase)
            .flatMap(s -> Optional.of(s + "!"));
        System.out.println("链式操作结果: " + result.orElse("无结果"));
        
        // 使用ifPresent
        present.ifPresent(s -> System.out.println("存在值: " + s));
        
        // 异常处理
        try {
            String mustExist = empty.orElseThrow(() -> new NoSuchElementException("值不存在"));
        } catch (NoSuchElementException e) {
            System.out.println("捕获异常: " + e.getMessage());
        }
        
        // Stream与Optional结合
        List<Optional<String>> optionals = Arrays.asList(
            Optional.of("A"),
            Optional.empty(),
            Optional.of("B"),
            Optional.empty(),
            Optional.of("C")
        );
        
        List<String> filtered = optionals.stream()
            .flatMap(Optional::stream)  // Java 9+: 过滤掉empty
            .collect(Collectors.toList());
        System.out.println("过滤后的值: " + filtered);
    }
    
    static String getNullableValue() {
        return Math.random() > 0.5 ? "Random Value" : null;
    }

    // ============================================
    // 6. 方法引用
    // ============================================
    
    static void demonstrateMethodReferences() {
        System.out.println("\n=== 方法引用演示 ===");
        
        List<String> words = Arrays.asList("apple", "banana", "cherry", "date");
        
        // 静态方法引用: ClassName::staticMethod
        List<Integer> lengths = words.stream()
            .map(String::length)
            .collect(Collectors.toList());
        System.out.println("长度列表: " + lengths);
        
        // 实例方法引用（特定对象）: object::instanceMethod
        String prefix = "Item: ";
        List<String> prefixed = words.stream()
            .map(prefix::concat)
            .collect(Collectors.toList());
        System.out.println("添加前缀: " + prefixed);
        
        // 实例方法引用（任意对象）: ClassName::instanceMethod
        List<String> upper = words.stream()
            .map(String::toUpperCase)
            .collect(Collectors.toList());
        System.out.println("大写: " + upper);
        
        // 构造方法引用: ClassName::new
        List<StringBuilder> builders = words.stream()
            .map(StringBuilder::new)
            .collect(Collectors.toList());
        System.out.println("StringBuilders: " + builders);
        
        // 数组构造方法引用: Type[]::new
        String[] array = words.stream()
            .toArray(String[]::new);
        System.out.println("数组: " + Arrays.toString(array));
        
        // 使用构造方法引用创建Map
        Map<String, Integer> map = words.stream()
            .collect(Collectors.toMap(
                Function.identity(),
                String::length,
                (v1, v2) -> v1,  // 处理冲突
                HashMap::new
            ));
        System.out.println("映射: " + map);
    }

    // ============================================
    // 7. 验证器组合
    // ============================================
    
    static void demonstrateValidatorComposition() {
        System.out.println("\n=== 验证器组合演示 ===");
        
        // 定义基础验证器
        Validator<String> notEmpty = s -> s != null && !s.isEmpty();
        Validator<String> minLength = s -> s != null && s.length() >= 3;
        Validator<String> hasDigits = s -> s != null && s.matches(".*\\d.*");
        
        // 组合验证器
        Validator<String> strongPassword = notEmpty
            .and(minLength)
            .and(hasDigits);
        
        // 测试
        String[] passwords = {"ab", "abc", "abc1", ""};
        for (String pwd : passwords) {
            System.out.printf("'%s' 是强密码: %b%n", pwd, strongPassword.validate(pwd));
        }
        
        // 灵活组合
        Validator<String> weakPassword = notEmpty.or(minLength);
        System.out.println("'ab' 通过弱验证: " + weakPassword.validate("ab"));
        
        // 否定
        Validator<String> isEmpty = notEmpty.negate();
        System.out.println("'' 是空: " + isEmpty.validate(""));
    }

    // ============================================
    // 主函数
    // ============================================
    
    public static void main(String[] args) {
        System.out.println("========================================");
        System.out.println("Java 函数式编程模式示例");
        System.out.println("========================================");
        
        demonstrateLambdas();
        demonstrateStreams();
        demonstrateAdvancedStreams();
        demonstrateOptional();
        demonstrateMethodReferences();
        demonstrateValidatorComposition();
        
        System.out.println("\n========================================");
        System.out.println("所有函数式演示完成");
        System.out.println("========================================");
    }
}
