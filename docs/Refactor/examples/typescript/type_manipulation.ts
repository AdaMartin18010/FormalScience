/**
 * TypeScript 类型操作高级技巧示例
 * 
 * 本文件演示TypeScript的类型系统：
 * - 条件类型
 * - 映射类型
 * - 模板字面量类型
 * - 类型推断
 */

// ============================================
// 1. 条件类型 (Conditional Types)
// ============================================

// 基础条件类型
type IsString<T> = T extends string ? true : false;

type A = IsString<string>;  // true
type B = IsString<number>;  // false

// 分布式条件类型
type ToArray<T> = T extends any ? T[] : never;
type StringOrNumberArray = ToArray<string | number>;  // string[] | number[]

// 非分布式条件类型（使用包裹）
type ToArrayNonDist<T> = [T] extends [any] ? T[] : never;
type BothArray = ToArrayNonDist<string | number>;  // (string | number)[]

// 实用条件类型
type Exclude<T, U> = T extends U ? never : T;
type Extract<T, U> = T extends U ? T : never;
type NonNullable<T> = T extends null | undefined ? never : T;

type T0 = Exclude<'a' | 'b' | 'c', 'a'>;  // 'b' | 'c'
type T1 = Extract<'a' | 'b' | 'c', 'a' | 'f'>;  // 'a'
type T2 = NonNullable<string | number | undefined>;  // string | number

// infer 关键字 - 类型推断
type ReturnType<T> = T extends (...args: any[]) => infer R ? R : never;
type Parameters<T> = T extends (...args: infer P) => any ? P : never;

function greet(name: string, age: number): string {
    return `Hello ${name}, you are ${age}`;
}

type GreetReturn = ReturnType<typeof greet>;  // string
type GreetParams = Parameters<typeof greet>;  // [string, number]

// 演示条件类型
function demonstrateConditionalTypes() {
    console.log("=== 条件类型演示 ===");
    
    // 使用 ReturnType
    const result: GreetReturn = "Hello";
    console.log("ReturnType 结果:", typeof result);
    
    // 使用 Parameters
    const params: GreetParams = ["Alice", 30];
    console.log("Parameters 结果:", params);
    
    // 类型守卫结合条件类型
    type IsArray<T> = T extends any[] ? true : false;
    
    function checkIsArray<T>(value: T): IsArray<T> {
        return Array.isArray(value) as IsArray<T>;
    }
    
    console.log("[1,2,3] 是数组:", checkIsArray([1, 2, 3]));
    console.log("'hello' 是数组:", checkIsArray("hello"));
}

demonstrateConditionalTypes();

// ============================================
// 2. 映射类型 (Mapped Types)
// ============================================

interface Person {
    name: string;
    age: number;
    address: string;
}

// 基础映射类型
type Readonly<T> = {
    readonly [P in keyof T]: T[P];
};

type Partial<T> = {
    [P in keyof T]?: T[P];
};

type Required<T> = {
    [P in keyof T]-?: T[P];  // -? 移除可选性
};

type Pick<T, K extends keyof T> = {
    [P in K]: T[P];
};

type Omit<T, K extends keyof any> = Pick<T, Exclude<keyof T, K>>;

// 使用映射类型
type ReadonlyPerson = Readonly<Person>;
type PartialPerson = Partial<Person>;
type PersonNameOnly = Pick<Person, 'name'>;
type PersonWithoutAddress = Omit<Person, 'address'>;

// 自定义映射类型
// 将所有属性变为可空
type Nullable<T> = {
    [P in keyof T]: T[P] | null;
};

// 将所有属性值转为字符串
type Stringify<T> = {
    [P in keyof T]: string;
};

// 重映射键名（TS 4.1+）
type Getters<T> = {
    [P in keyof T as `get${Capitalize<string & P>}`]: () => T[P];
};

type Setters<T> = {
    [P in keyof T as `set${Capitalize<string & P>}`]: (value: T[P]) => void;
};

type PersonAccessors = Getters<Person> & Setters<Person>;

// 演示映射类型
function demonstrateMappedTypes() {
    console.log("\n=== 映射类型演示 ===");
    
    // Partial 使用
    const partialPerson: PartialPerson = { name: "Alice" };
    console.log("Partial Person:", partialPerson);
    
    // Pick 使用
    const nameOnly: PersonNameOnly = { name: "Bob" };
    console.log("Name Only:", nameOnly);
    
    // Omit 使用
    const withoutAddress: PersonWithoutAddress = { name: "Charlie", age: 30 };
    console.log("Without Address:", withoutAddress);
    
    // Nullable 使用
    type NullablePerson = Nullable<Person>;
    const nullablePerson: NullablePerson = {
        name: null,
        age: 25,
        address: null
    };
    console.log("Nullable Person:", nullablePerson);
    
    // Getters 使用
    const personAccessors: PersonAccessors = {
        getName: () => "David",
        getAge: () => 35,
        getAddress: () => "123 Main St",
        setName: (value) => console.log("Setting name to:", value),
        setAge: (value) => console.log("Setting age to:", value),
        setAddress: (value) => console.log("Setting address to:", value)
    };
    console.log("Getter name:", personAccessors.getName());
}

demonstrateMappedTypes();

// ============================================
// 3. 模板字面量类型 (Template Literal Types)
// ============================================

// 基础模板字面量
type EventName<T extends string> = `on${Capitalize<T>}`;
type ClickEvent = EventName<'click'>;  // 'onClick'
type HoverEvent = EventName<'hover'>;  // 'onHover'

// 组合多个模板
type HTTPMethod = 'get' | 'post' | 'put' | 'delete';
type Endpoint<T extends string> = `/api/${T}`;
type APIEndpoint = Endpoint<'users' | 'posts' | 'comments'>;

// 泛型模板字面量
type Action<T extends string, U extends string> = `${T}_${U}`;
type UserAction = Action<'USER', 'CREATE' | 'UPDATE' | 'DELETE'>;

// 内置字符串操作类型
type UppercaseS = Uppercase<'hello'>;      // 'HELLO'
type LowercaseS = Lowercase<'WORLD'>;      // 'world'
type CapitalizeS = Capitalize<'type'>;     // 'Type'
type UncapitalizeS = Uncapitalize<'Script'>;  // 'script'

// 递归模板类型
type DeepPartial<T> = {
    [P in keyof T]?: T[P] extends object ? DeepPartial<T[P]> : T[P];
};

interface Company {
    name: string;
    employees: {
        name: string;
        department: {
            name: string;
            budget: number;
        };
    }[];
}

type PartialCompany = DeepPartial<Company>;

// 演示模板字面量类型
function demonstrateTemplateLiterals() {
    console.log("\n=== 模板字面量类型演示 ===");
    
    // 事件处理器类型
    type EventHandlers<T extends string> = {
        [K in T as `on${Capitalize<K>}`]: (event: Event) => void;
    };
    
    type ButtonEvents = EventHandlers<'click' | 'dblclick' | 'mouseover'>;
    
    const handlers: ButtonEvents = {
        onClick: (e) => console.log("Clicked"),
        onDblclick: (e) => console.log("Double clicked"),
        onMouseover: (e) => console.log("Mouse over")
    };
    console.log("事件处理器定义完成");
    
    // CSS属性类型
    type CSSProperty = 'color' | 'background' | 'font-size';
    type CSSVariable<T extends string> = `--${KebabCase<T>}`;
    
    type KebabCase<S extends string> = S extends `${infer T}${infer U}`
        ? `${Lowercase<T>}${U extends Capitalize<U> ? `-${KebabCase<Lowercase<U>>}` : KebabCase<U>}`
        : S;
    
    type TestKebab = KebabCase<'backgroundColor'>;  // 'background-color'
    
    // 对象路径类型
    type Path<T, K extends keyof T = keyof T> = K extends string
        ? T[K] extends Record<string, any>
            ? `${K}` | `${K}.${Path<T[K]>}`
            : `${K}`
        : never;
    
    type CompanyPath = Path<Company>;
    const validPath: CompanyPath = "employees.0.department.name";
    console.log("对象路径:", validPath);
}

demonstrateTemplateLiterals();

// ============================================
// 4. 类型推断与类型守卫
// ============================================

// typeof 类型守卫
function processValue(value: string | number | boolean) {
    if (typeof value === 'string') {
        return value.toUpperCase();  // TypeScript知道这里是string
    } else if (typeof value === 'number') {
        return value.toFixed(2);     // TypeScript知道这里是number
    } else {
        return value ? 'YES' : 'NO'; // TypeScript知道这里是boolean
    }
}

// instanceof 类型守卫
class Cat {
    meow() { return 'Meow!'; }
}

class Dog {
    bark() { return 'Woof!'; }
}

function makeSound(animal: Cat | Dog) {
    if (animal instanceof Cat) {
        return animal.meow();
    } else {
        return animal.bark();
    }
}

// 自定义类型守卫
type Fish = { swim: () => void };
type Bird = { fly: () => void };

function isFish(pet: Fish | Bird): pet is Fish {
    return (pet as Fish).swim !== undefined;
}

function move(pet: Fish | Bird) {
    if (isFish(pet)) {
        pet.swim();
    } else {
        pet.fly();
    }
}

// 判别联合类型
interface Square {
    kind: 'square';
    size: number;
}

interface Circle {
    kind: 'circle';
    radius: number;
}

interface Triangle {
    kind: 'triangle';
    base: number;
    height: number;
}

type Shape = Square | Circle | Triangle;

function getArea(shape: Shape): number {
    switch (shape.kind) {
        case 'square':
            return shape.size ** 2;
        case 'circle':
            return Math.PI * shape.radius ** 2;
        case 'triangle':
            return 0.5 * shape.base * shape.height;
        default:
            // 穷尽检查
            const _exhaustiveCheck: never = shape;
            return _exhaustiveCheck;
    }
}

// 类型推断工具
type InferArray<T> = T extends (infer U)[] ? U : never;
type InferPromise<T> = T extends Promise<infer U> ? U : never;
type InferFunction<T> = T extends (...args: any[]) => infer R ? R : never;

type Num = InferArray<number[]>;           // number
type Str = InferPromise<Promise<string>>;  // string
type Bool = InferFunction<() => boolean>;  // boolean

// 演示类型推断
function demonstrateTypeInference() {
    console.log("\n=== 类型推断演示 ===");
    
    // typeof 守卫
    console.log("String:", processValue("hello"));
    console.log("Number:", processValue(42));
    console.log("Boolean:", processValue(true));
    
    // instanceof 守卫
    const cat = new Cat();
    const dog = new Dog();
    console.log("Cat sound:", makeSound(cat));
    console.log("Dog sound:", makeSound(dog));
    
    // 判别联合
    const square: Shape = { kind: 'square', size: 5 };
    const circle: Shape = { kind: 'circle', radius: 3 };
    console.log("Square area:", getArea(square));
    console.log("Circle area:", getArea(circle));
}

demonstrateTypeInference();

// ============================================
// 5. 高级类型工具
// ============================================

// 深度只读
type DeepReadonly<T> = {
    readonly [P in keyof T]: T[P] extends object 
        ? DeepReadonly<T[P]> 
        : T[P];
};

// 扁平化类型
type Flatten<T> = T extends Array<infer U> ? Flatten<U> : T;

type NestedArray = number[][][];
type Flattened = Flatten<NestedArray>;  // number

// 必选属性键
type RequiredKeys<T> = {
    [K in keyof T]-?: {} extends Pick<T, K> ? never : K;
}[keyof T];

// 可选属性键
type OptionalKeys<T> = {
    [K in keyof T]-?: {} extends Pick<T, K> ? K : never;
}[keyof T];

// 元组转联合类型
type TupleToUnion<T extends any[]> = T[number];
type MyTuple = [1, 2, 3];
type MyUnion = TupleToUnion<MyTuple>;  // 1 | 2 | 3

// 联合类型转交叉类型
type UnionToIntersection<U> = 
    (U extends any ? (k: U) => void : never) extends (k: infer I) => void 
        ? I 
        : never;

type Union = { a: string } | { b: number };
type Intersection = UnionToIntersection<Union>;  // { a: string } & { b: number }

// 演示高级类型工具
function demonstrateAdvancedTools() {
    console.log("\n=== 高级类型工具演示 ===");
    
    // DeepReadonly
    type ReadonlyCompany = DeepReadonly<Company>;
    const readonlyCompany: ReadonlyCompany = {
        name: "TechCorp",
        employees: []
    };
    console.log("DeepReadonly 创建成功");
    
    // RequiredKeys / OptionalKeys
    interface Mixed {
        required1: string;
        required2: number;
        optional1?: boolean;
        optional2?: Date;
    }
    
    type ReqKeys = RequiredKeys<Mixed>;  // 'required1' | 'required2'
    type OptKeys = OptionalKeys<Mixed>;  // 'optional1' | 'optional2'
    
    console.log("Required keys 类型检查通过");
    console.log("Optional keys 类型检查通过");
    
    // UnionToIntersection
    type Result = UnionToIntersection<{ x: 1 } | { y: 2 }>;
    const result: Result = { x: 1, y: 2 };
    console.log("UnionToIntersection 结果:", result);
}

demonstrateAdvancedTools();

// ============================================
// 6. 类型级编程
// ============================================

// 斐波那契数列（类型级别）
type Fibonacci<N extends number, Sequence extends any[] = [1, 1]> = 
    Sequence['length'] extends N 
        ? Sequence 
        : Fibonacci<N, [...Sequence, Add<Last<Sequence>, SecondLast<Sequence>>]>;

type Last<T extends any[]> = T extends [...any[], infer L] ? L : never;
type SecondLast<T extends any[]> = T extends [...any[], infer S, any] ? S : never;

// 简单数字加法（通过数组长度）
type BuildTuple<N extends number, Result extends any[] = []> = 
    Result['length'] extends N 
        ? Result 
        : BuildTuple<N, [...Result, any]>;

type Add<A extends number, B extends number> = 
    [...BuildTuple<A>, ...BuildTuple<B>]['length'] extends infer R 
        ? R extends number ? R : never 
        : never;

// 类型安全的数组长度
type FixedArray<T, N extends number> = {
    [K in keyof BuildTuple<N>]: T;
};

// 长度检查
function createFixedArray<T, N extends number>(length: N): FixedArray<T, N> {
    return new Array(length) as FixedArray<T, N>;
}

// 演示类型级编程
function demonstrateTypeLevelProgramming() {
    console.log("\n=== 类型级编程演示 ===");
    
    // 固定长度数组
    const arr3 = createFixedArray<number, 3>(3);
    arr3[0] = 1;
    arr3[1] = 2;
    arr3[2] = 3;
    // arr3[3] = 4;  // 编译错误：索引越界
    
    console.log("固定长度数组:", arr3);
    
    // 类型安全的配置对象
    type Config<T extends Record<string, any>> = {
        [K in keyof T]: T[K] extends (...args: any[]) => any 
            ? ReturnType<T[K]> 
            : T[K];
    };
    
    const config: Config<{
        name: string;
        getValue: () => number;
        transform: (x: string) => boolean;
    }> = {
        name: "test",
        getValue: 42,
        transform: true
    };
    
    console.log("Config:", config);
}

demonstrateTypeLevelProgramming();

console.log("\n========================================");
console.log("TypeScript 类型操作演示完成");
console.log("========================================");
