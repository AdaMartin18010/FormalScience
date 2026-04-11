/**
 * C++ 类型特征与模板元编程示例
 * 
 * 本文件演示现代C++中的类型系统：
 * - 类型萃取（Type Traits）
 * - SFINAE技巧
 * - 概念约束（Concepts - C++20）
 * - 编译期计算
 */

#include <iostream>
#include <type_traits>
#include <vector>
#include <string>
#include <concepts>  // C++20
#include <array>

// ============================================
// 1. 基础类型特征
// ============================================

// 检查类型属性
void demonstrate_basic_type_traits() {
    std::cout << "=== 基础类型特征 ===\n";
    
    // 检查是否为整数类型
    std::cout << "int 是整数: " << std::is_integral_v<int> << "\n";
    std::cout << "double 是整数: " << std::is_integral_v<double> << "\n";
    
    // 检查是否为浮点类型
    std::cout << "float 是浮点: " << std::is_floating_point_v<float> << "\n";
    std::cout << "int 是浮点: " << std::is_floating_point_v<int> << "\n";
    
    // 检查是否为指针
    std::cout << "int* 是指针: " << std::is_pointer_v<int*> << "\n";
    std::cout << "int 是指针: " << std::is_pointer_v<int> << "\n";
    
    // 检查是否为数组
    std::cout << "int[5] 是数组: " << std::is_array_v<int[5]> << "\n";
    
    // 检查是否为类类型
    struct MyClass {};
    std::cout << "MyClass 是类: " << std::is_class_v<MyClass> << "\n";
    std::cout << "int 是类: " << std::is_class_v<int> << "\n";
}

// ============================================
// 2. 类型修改器
// ============================================

void demonstrate_type_modifiers() {
    std::cout << "\n=== 类型修改器 ===\n";
    
    // 移除const
    using T1 = std::remove_const_t<const int>;
    std::cout << "remove_const<const int> 是 int: " 
              << std::is_same_v<T1, int> << "\n";
    
    // 移除引用
    using T2 = std::remove_reference_t<int&>;
    std::cout << "remove_reference<int&> 是 int: " 
              << std::is_same_v<T2, int> << "\n";
    
    // 添加const
    using T3 = std::add_const_t<int>;
    std::cout << "add_const<int> 是 const int: " 
              << std::is_same_v<T3, const int> << "\n";
    
    // 条件类型
    using T4 = std::conditional_t<true, int, double>;
    using T5 = std::conditional_t<false, int, double>;
    std::cout << "conditional_t<true, int, double> 是 int: " 
              << std::is_same_v<T4, int> << "\n";
    std::cout << "conditional_t<false, int, double> 是 double: " 
              << std::is_same_v<T5, double> << "\n";
}

// ============================================
// 3. SFINAE (Substitution Failure Is Not An Error)
// ============================================

// 使用SFINAE启用/禁用函数模板

// 检查类型是否有begin()成员函数
template<typename T>
class has_begin {
    template<typename U>
    static auto test(int) -> decltype(std::declval<U>().begin(), std::true_type());
    
    template<typename>
    static std::false_type test(...);
    
public:
    static constexpr bool value = decltype(test<T>(0))::value;
};

// 使用SFINAE根据类型特性选择函数
// 版本1：适用于有begin()的类型（容器）
template<typename T>
std::enable_if_t<has_begin<T>::value, void>
print_elements(const T& container) {
    std::cout << "容器内容: ";
    for (const auto& elem : container) {
        std::cout << elem << " ";
    }
    std::cout << "\n";
}

// 版本2：适用于没有begin()的类型（单个值）
template<typename T>
std::enable_if_t<!has_begin<T>::value, void>
print_elements(const T& value) {
    std::cout << "单个值: " << value << "\n";
}

// 使用std::void_t简化SFINAE
template<typename, typename = std::void_t<>>
struct has_foo_member : std::false_type {};

template<typename T>
struct has_foo_member<T, std::void_t<decltype(std::declval<T>().foo)>> 
    : std::true_type {};

struct WithFoo { void foo() {} };
struct WithoutFoo {};

void demonstrate_sfinae() {
    std::cout << "\n=== SFINAE 技巧 ===\n";
    
    // 检查has_begin
    std::cout << "vector 有 begin(): " << has_begin<std::vector<int>>::value << "\n";
    std::cout << "int 有 begin(): " << has_begin<int>::value << "\n";
    
    // 使用重载函数
    std::vector<int> vec = {1, 2, 3};
    print_elements(vec);  // 调用容器版本
    print_elements(42);   // 调用单个值版本
    
    // 检查has_foo_member
    std::cout << "WithFoo 有 foo: " << has_foo_member<WithFoo>::value << "\n";
    std::cout << "WithoutFoo 有 foo: " << has_foo_member<WithoutFoo>::value << "\n";
}

// ============================================
// 4. 编译期计算
// ============================================

// 编译期阶乘（C++14 constexpr）
constexpr int factorial(int n) {
    return n <= 1 ? 1 : n * factorial(n - 1);
}

// 编译期斐波那契数列
template<int N>
struct Fibonacci {
    static constexpr int value = Fibonacci<N-1>::value + Fibonacci<N-2>::value;
};

template<>
struct Fibonacci<0> {
    static constexpr int value = 0;
};

template<>
struct Fibonacci<1> {
    static constexpr int value = 1;
};

// 编译期类型列表
template<typename... Types>
struct TypeList {
    static constexpr size_t size = sizeof...(Types);
};

// 获取类型列表中的第N个类型
template<size_t N, typename List>
struct TypeAt;

template<size_t N, typename First, typename... Rest>
struct TypeAt<N, TypeList<First, Rest...>> {
    using type = typename TypeAt<N-1, TypeList<Rest...>>::type;
};

template<typename First, typename... Rest>
struct TypeAt<0, TypeList<First, Rest...>> {
    using type = First;
};

// 编译期整数序列
template<size_t... Is>
struct IndexSequence {};

template<size_t N, size_t... Is>
struct MakeIndexSequence : MakeIndexSequence<N-1, N-1, Is...> {};

template<size_t... Is>
struct MakeIndexSequence<0, Is...> {
    using type = IndexSequence<Is...>;
};

void demonstrate_compile_time_computation() {
    std::cout << "\n=== 编译期计算 ===\n";
    
    // 编译期阶乘
    constexpr int fact5 = factorial(5);
    std::cout << "5! = " << fact5 << " (编译期计算)\n";
    
    static_assert(factorial(0) == 1, "0! 应该等于 1");
    static_assert(factorial(5) == 120, "5! 应该等于 120");
    
    // 编译期斐波那契
    std::cout << "Fibonacci(10) = " << Fibonacci<10>::value << "\n";
    static_assert(Fibonacci<10>::value == 55, "Fib(10) 应该等于 55");
    
    // 类型列表
    using MyTypes = TypeList<int, double, char, std::string>;
    std::cout << "类型列表大小: " << MyTypes::size << "\n";
    
    using ThirdType = TypeAt<2, MyTypes>::type;
    std::cout << "第3个类型是 char: " << std::is_same_v<ThirdType, char> << "\n";
}

// ============================================
// 5. C++20 概念（Concepts）
// ============================================

// C++20: 定义概念
// 可相加概念
template<typename T>
concept Addable = requires(T a, T b) {
    { a + b } -> std::convertible_to<T>;
};

// 可比较概念
template<typename T>
concept Comparable = requires(T a, T b) {
    { a < b } -> std::convertible_to<bool>;
    { a == b } -> std::convertible_to<bool>;
};

// 容器概念
template<typename T>
concept Container = requires(T t) {
    typename T::value_type;
    { t.begin() } -> std::same_as<typename T::iterator>;
    { t.end() } -> std::same_as<typename T::iterator>;
    { t.size() } -> std::convertible_to<std::size_t>;
};

// 使用概念的函数
template<Addable T>
T add(T a, T b) {
    return a + b;
}

// 简写语法 (C++20)
auto max_value(Comparable auto a, Comparable auto b) {
    return (a < b) ? b : a;
}

// 概念约束模板类
template<Comparable T>
class OrderedPair {
public:
    OrderedPair(T first, T second) 
        : first_(std::min(first, second))
        , second_(std::max(first, second)) {}
    
    T first() const { return first_; }
    T second() const { return second_; }
    
private:
    T first_, second_;
};

// 使用标准库概念
template<typename Container>
requires std::ranges::range<Container>
void print_range(const Container& c) {
    std::cout << "范围内容: ";
    for (const auto& elem : c) {
        std::cout << elem << " ";
    }
    std::cout << "\n";
}

void demonstrate_concepts() {
    std::cout << "\n=== C++20 概念 ===\n";
    
    // Addable 概念
    std::cout << "add(3, 4) = " << add(3, 4) << "\n";
    std::cout << "add(2.5, 3.5) = " << add(2.5, 3.5) << "\n";
    std::cout << "add(string, string) = " << add(std::string("Hello, "), std::string("World!")) << "\n";
    
    // Comparable 概念
    std::cout << "max_value(10, 20) = " << max_value(10, 20) << "\n";
    std::cout << "max_value(3.14, 2.71) = " << max_value(3.14, 2.71) << "\n";
    
    // OrderedPair
    OrderedPair<int> pair(30, 10);
    std::cout << "OrderedPair(30, 10): first=" << pair.first() 
              << ", second=" << pair.second() << "\n";
    
    // print_range
    std::vector<int> vec = {1, 2, 3, 4, 5};
    print_range(vec);
}

// ============================================
// 6. 高级模板技巧
// ============================================

// CRTP (Curiously Recurring Template Pattern)
template<typename Derived>
class Base {
public:
    void interface() {
        static_cast<Derived*>(this)->implementation();
    }
    
    void default_implementation() {
        std::cout << "默认实现\n";
    }
};

class Derived1 : public Base<Derived1> {
public:
    void implementation() {
        std::cout << "Derived1 实现\n";
    }
};

class Derived2 : public Base<Derived2> {
public:
    void implementation() {
        std::cout << "Derived2 实现\n";
    }
};

// 表达式模板（简化示例）
template<typename Derived>
class Expression {
public:
    auto eval() const {
        return static_cast<const Derived&>(*this).eval();
    }
};

template<typename LHS, typename RHS>
class AddExpr : public Expression<AddExpr<LHS, RHS>> {
    const LHS& lhs_;
    const RHS& rhs_;
public:
    AddExpr(const LHS& l, const RHS& r) : lhs_(l), rhs_(r) {}
    auto eval() const { return lhs_.eval() + rhs_.eval(); }
};

class Value : public Expression<Value> {
    double value_;
public:
    Value(double v) : value_(v) {}
    double eval() const { return value_; }
};

template<typename LHS, typename RHS>
AddExpr<LHS, RHS> operator+(const Expression<LHS>& l, const Expression<RHS>& r) {
    return AddExpr<LHS, RHS>(static_cast<const LHS&>(l), static_cast<const RHS&>(r));
}

void demonstrate_advanced_templates() {
    std::cout << "\n=== 高级模板技巧 ===\n";
    
    // CRTP
    Derived1 d1;
    Derived2 d2;
    d1.interface();
    d2.interface();
    
    // 表达式模板
    Value a(1.0), b(2.0), c(3.0);
    auto expr = a + b + c;
    std::cout << "表达式 (1 + 2 + 3) = " << expr.eval() << "\n";
}

// ============================================
// 主函数
// ============================================

int main() {
    std::cout << "========================================\n";
    std::cout << "C++ 类型特征与模板元编程示例\n";
    std::cout << "========================================\n";
    
    demonstrate_basic_type_traits();
    demonstrate_type_modifiers();
    demonstrate_sfinae();
    demonstrate_compile_time_computation();
    demonstrate_concepts();
    demonstrate_advanced_templates();
    
    std::cout << "\n========================================\n";
    std::cout << "所有类型特征演示完成\n";
    std::cout << "========================================\n";
    
    return 0;
}
