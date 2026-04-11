import java.util.*;
import java.lang.reflect.*;

/**
 * Java 类型系统高级特性示例
 * 
 * 本文件演示Java类型系统的高级特性：
 * - 泛型通配符
 * - 类型边界
 * - 类型擦除
 * - 可变参数和类型安全
 */
public class TypeSystem {

    // ============================================
    // 1. 泛型基础回顾
    // ============================================
    
    static class Box<T> {
        private T content;
        
        public void set(T content) {
            this.content = content;
        }
        
        public T get() {
            return content;
        }
        
        public <U> U transform(java.util.function.Function<T, U> converter) {
            return converter.apply(content);
        }
    }
    
    static void demonstrateBasicGenerics() {
        System.out.println("=== 泛型基础 ===");
        
        // 类型安全
        Box<Integer> intBox = new Box<>();
        intBox.set(42);
        int value = intBox.get();  // 不需要强制转换
        System.out.println("整型盒子: " + value);
        
        Box<String> strBox = new Box<>();
        strBox.set("Hello");
        String text = strBox.get();
        System.out.println("字符串盒子: " + text);
        
        // 泛型方法
        Integer length = strBox.transform(String::length);
        System.out.println("转换结果: " + length);
    }

    // ============================================
    // 2. 通配符详解
    // ============================================
    
    static class Animal {
        void speak() { System.out.println("Animal speaks"); }
    }
    
    static class Dog extends Animal {
        void speak() { System.out.println("Dog barks"); }
        void wagTail() { System.out.println("Dog wags tail"); }
    }
    
    static class Cat extends Animal {
        void speak() { System.out.println("Cat meows"); }
    }
    
    static void demonstrateWildcards() {
        System.out.println("\n=== 通配符详解 ===");
        
        // <? extends T>: 上界通配符，只读
        List<? extends Animal> animals;
        
        List<Dog> dogs = new ArrayList<>();
        dogs.add(new Dog());
        animals = dogs;  // OK: List<Dog> 可以赋值给 List<? extends Animal>
        
        // animals.add(new Dog());  // 编译错误：不能添加
        // animals.add(new Animal());  // 编译错误：不能添加
        // 原因：animals可能是 List<Cat>，添加 Dog 会破坏类型安全
        
        for (Animal a : animals) {
            a.speak();  // OK: 可以读取，类型至少是 Animal
        }
        
        // <? super T>: 下界通配符，可写
        List<? super Dog> dogSupers;
        
        List<Animal> animalList = new ArrayList<>();
        dogSupers = animalList;  // OK: List<Animal> 可以赋值给 List<? super Dog>
        
        dogSupers.add(new Dog());  // OK: 可以添加 Dog 或其子类
        // Dog d = dogSupers.get(0);  // 编译错误：获取的类型不确定
        Object obj = dogSupers.get(0);  // OK: 只能当作 Object
        
        // PECS原则: Producer-Extends, Consumer-Super
        // extends: 作为生产者，提供数据（读取）
        // super: 作为消费者，接收数据（写入）
    }
    
    // 使用PECS原则的方法
    static <T> void copy(List<? extends T> src, List<? super T> dest) {
        for (T item : src) {
            dest.add(item);
        }
    }
    
    static void demonstratePECS() {
        System.out.println("\n=== PECS原则演示 ===");
        
        List<Dog> dogs = Arrays.asList(new Dog(), new Dog());
        List<Animal> animals = new ArrayList<>();
        
        // 从 dogs (生产者) 复制到 animals (消费者)
        copy(dogs, animals);
        
        System.out.println("复制后动物数量: " + animals.size());
        for (Animal a : animals) {
            a.speak();
        }
    }

    // ============================================
    // 3. 类型边界
    // ============================================
    
    // 上界: T 必须是 Number 或其子类
    static class NumberBox<T extends Number> {
        private T number;
        
        public NumberBox(T number) {
            this.number = number;
        }
        
        public double doubleValue() {
            return number.doubleValue();
        }
        
        // 多重边界: T 必须是 Number 的子类且实现 Comparable
        public static <T extends Number & Comparable<T>> T max(T a, T b) {
            return a.compareTo(b) > 0 ? a : b;
        }
    }
    
    // 递归类型边界
    interface Comparable<T> {
        int compareTo(T other);
    }
    
    static class Node<T extends Comparable<T>> {
        T value;
        Node<T> left, right;
        
        Node(T value) {
            this.value = value;
        }
        
        void insert(T newValue) {
            int cmp = ((java.lang.Comparable<T>) value).compareTo(newValue);
            if (cmp > 0) {
                if (left == null) left = new Node<>(newValue);
                else left.insert(newValue);
            } else {
                if (right == null) right = new Node<>(newValue);
                else right.insert(newValue);
            }
        }
    }
    
    static void demonstrateBounds() {
        System.out.println("\n=== 类型边界演示 ===");
        
        // 上界
        NumberBox<Integer> intBox = new NumberBox<>(42);
        NumberBox<Double> doubleBox = new NumberBox<>(3.14);
        System.out.println("Integer值: " + intBox.doubleValue());
        System.out.println("Double值: " + doubleBox.doubleValue());
        
        // NumberBox<String> strBox;  // 编译错误：String不是Number的子类
        
        // 多重边界
        Integer maxInt = NumberBox.max(10, 20);
        Double maxDouble = NumberBox.max(2.5, 3.5);
        System.out.println("最大整数: " + maxInt);
        System.out.println("最大浮点数: " + maxDouble);
    }

    // ============================================
    // 4. 类型擦除
    // ============================================
    
    static void demonstrateTypeErasure() {
        System.out.println("\n=== 类型擦除演示 ===");
        
        // 编译后泛型类型信息被擦除
        List<String> strList = new ArrayList<>();
        List<Integer> intList = new ArrayList<>();
        
        // 运行时类型相同
        System.out.println("运行时类型相同: " + strList.getClass().equals(intList.getClass()));
        System.out.println("类名: " + strList.getClass().getName());
        
        // 通过反射可以绕过泛型检查（危险！）
        try {
            Method addMethod = strList.getClass().getMethod("add", Object.class);
            addMethod.invoke(strList, 42);  // 添加整数到字符串列表！
            System.out.println("通过反射添加后: " + strList);
            
            // 这会在运行时抛出 ClassCastException
            // String s = strList.get(0);
        } catch (Exception e) {
            e.printStackTrace();
        }
        
        // 桥方法演示
        class StringNode extends Node<String> {
            StringNode(String value) {
                super(value);
            }
            
            // 编译器会生成桥方法来保持多态性
            @Override
            void insert(String newValue) {
                System.out.println("插入字符串: " + newValue);
                super.insert(newValue);
            }
        }
        
        // 获取桥方法
        try {
            Method[] methods = StringNode.class.getDeclaredMethods();
            System.out.println("\nStringNode方法:");
            for (Method m : methods) {
                System.out.println("  " + m.getName() + " - synthetic: " + m.isSynthetic());
            }
        } catch (Exception e) {
            e.printStackTrace();
        }
    }

    // ============================================
    // 5. 泛型数组限制与解决方案
    // ============================================
    
    static <T> T[] createGenericArray(int size, T prototype) {
        // 不能直接创建: return new T[size];  // 编译错误
        
        // 解决方案1: 使用 Object[] 然后强制转换
        @SuppressWarnings("unchecked")
        T[] array = (T[]) java.lang.reflect.Array.newInstance(
            prototype.getClass(), size);
        return array;
    }
    
    // 更好的解决方案: 使用 List
    static class GenericList<T> {
        private final List<T> elements = new ArrayList<>();
        
        public void add(T element) {
            elements.add(element);
        }
        
        public T get(int index) {
            return elements.get(index);
        }
        
        @SuppressWarnings("unchecked")
        public T[] toArray(Class<T> clazz) {
            return elements.toArray((T[]) java.lang.reflect.Array.newInstance(clazz, 0));
        }
    }
    
    static void demonstrateGenericArrays() {
        System.out.println("\n=== 泛型数组解决方案 ===");
        
        // 使用反射创建
        String[] strArray = createGenericArray(5, "");
        strArray[0] = "Hello";
        System.out.println("创建泛型数组: " + Arrays.toString(strArray));
        
        // 使用包装类
        GenericList<Integer> list = new GenericList<>();
        list.add(1);
        list.add(2);
        list.add(3);
        Integer[] array = list.toArray(Integer.class);
        System.out.println("转换为数组: " + Arrays.toString(array));
    }

    // ============================================
    // 6. 可变参数与堆污染
    // ============================================
    
    // 安全的可变参数方法
    @SafeVarargs
    static <T> List<T> asList(T... elements) {
        return Arrays.asList(elements);
    }
    
    // 危险的可变参数方法
    @SuppressWarnings("unchecked")
    static void dangerousVarargs(List<String>... lists) {
        // 堆污染警告：lists实际上是一个List[]
        Object[] array = lists;
        
        // 可以添加不同类型的List，破坏类型安全
        // array[0] = Arrays.asList(1, 2, 3);  // 可能导致运行时错误
        
        for (List<String> list : lists) {
            for (String s : list) {
                System.out.println(s);
            }
        }
    }
    
    // 安全的模式
    @SafeVarargs
    static <T> void safeProcess(T... elements) {
        // 不对 elements 数组做任何修改
        for (T element : elements) {
            System.out.println(element);
        }
    }
    
    static void demonstrateVarargs() {
        System.out.println("\n=== 可变参数演示 ===");
        
        List<String> list1 = asList("A", "B", "C");
        List<Integer> list2 = asList(1, 2, 3);
        System.out.println("字符串列表: " + list1);
        System.out.println("整数列表: " + list2);
        
        // 安全使用
        safeProcess("Hello", "World", "!");
        safeProcess(1, 2, 3, 4, 5);
    }

    // ============================================
    // 7. 高级类型模式
    // ============================================
    
    // 自限定类型
    static abstract class SelfBounded<T extends SelfBounded<T>> {
        abstract T self();
        
        T doSomething() {
            System.out.println("做某事");
            return self();
        }
    }
    
    static class ConcreteSelf extends SelfBounded<ConcreteSelf> {
        @Override
        ConcreteSelf self() {
            return this;
        }
        
        ConcreteSelf specificMethod() {
            System.out.println("特定方法");
            return this;
        }
    }
    
    // 类型令牌
    static class TypeToken<T> {
        private final Class<T> type;
        
        @SuppressWarnings("unchecked")
        TypeToken() {
            // 获取运行时类型信息
            this.type = (Class<T>) ((ParameterizedType) getClass()
                .getGenericSuperclass()).getActualTypeArguments()[0];
        }
        
        Class<T> getType() {
            return type;
        }
        
        boolean isInstance(Object obj) {
            return type.isInstance(obj);
        }
    }
    
    static void demonstrateAdvancedPatterns() {
        System.out.println("\n=== 高级类型模式 ===");
        
        // 自限定类型
        ConcreteSelf cs = new ConcreteSelf();
        cs.doSomething().specificMethod();  // 方法链返回正确类型
        
        // 类型令牌
        TypeToken<String> stringToken = new TypeToken<>() {};
        System.out.println("类型令牌: " + stringToken.getType().getName());
        System.out.println("'hello' 是 String: " + stringToken.isInstance("hello"));
        System.out.println("42 是 String: " + stringToken.isInstance(42));
    }

    // ============================================
    // 主函数
    // ============================================
    
    public static void main(String[] args) {
        System.out.println("========================================");
        System.out.println("Java 类型系统高级特性示例");
        System.out.println("========================================");
        
        demonstrateBasicGenerics();
        demonstrateWildcards();
        demonstratePECS();
        demonstrateBounds();
        demonstrateTypeErasure();
        demonstrateGenericArrays();
        demonstrateVarargs();
        demonstrateAdvancedPatterns();
        
        System.out.println("\n========================================");
        System.out.println("所有类型系统演示完成");
        System.out.println("========================================");
    }
}
