/**
 * TypeScript 函数式工具实现示例
 * 
 * 本文件演示函数式编程工具：
 * - 高阶函数
 * - 函数组合
 * - 柯里化
 * - Monad模式
 */

// ============================================
// 1. 高阶函数
// ============================================

// 记忆化函数（Memoization）
function memoize<T extends (...args: any[]) => any>(fn: T): T {
    const cache = new Map<string, ReturnType<T>>();
    
    return ((...args: Parameters<T>): ReturnType<T> => {
        const key = JSON.stringify(args);
        
        if (cache.has(key)) {
            return cache.get(key)!;
        }
        
        const result = fn(...args);
        cache.set(key, result);
        return result;
    }) as T;
}

// 计算斐波那契数（带记忆化）
const fibonacci = memoize((n: number): number => {
    if (n <= 1) return n;
    return fibonacci(n - 1) + fibonacci(n - 2);
});

// 节流函数（Throttle）
function throttle<T extends (...args: any[]) => any>(
    fn: T, 
    limit: number
): (...args: Parameters<T>) => void {
    let inThrottle = false;
    
    return (...args: Parameters<T>): void => {
        if (!inThrottle) {
            fn(...args);
            inThrottle = true;
            setTimeout(() => inThrottle = false, limit);
        }
    };
}

// 防抖函数（Debounce）
function debounce<T extends (...args: any[]) => any>(
    fn: T, 
    delay: number
): (...args: Parameters<T>) => void {
    let timeoutId: ReturnType<typeof setTimeout> | null = null;
    
    return (...args: Parameters<T>): void => {
        if (timeoutId) clearTimeout(timeoutId);
        timeoutId = setTimeout(() => fn(...args), delay);
    };
}

// 偏函数应用
function partial<T, Args extends any[], Rest extends any[], R>(
    fn: (...args: [...Args, ...Rest]) => R,
    ...presetArgs: Args
): (...remainingArgs: Rest) => R {
    return (...remainingArgs: Rest): R => 
        fn(...presetArgs, ...remainingArgs);
}

// 管道函数
function pipe<T>(value: T): T;
function pipe<T, U>(value: T, fn1: (x: T) => U): U;
function pipe<T, U, V>(value: T, fn1: (x: T) => U, fn2: (x: U) => V): V;
function pipe<T, U, V, W>(value: T, fn1: (x: T) => U, fn2: (x: U) => V, fn3: (x: V) => W): W;
function pipe<T, U, V, W, X>(value: T, fn1: (x: T) => U, fn2: (x: U) => V, fn3: (x: V) => W, fn4: (x: W) => X): X;
function pipe(value: any, ...fns: Array<(x: any) => any>): any {
    return fns.reduce((acc, fn) => fn(acc), value);
}

// 演示高阶函数
function demonstrateHigherOrderFunctions() {
    console.log("=== 高阶函数演示 ===");
    
    // 记忆化演示
    console.time("fib(35) 第一次");
    console.log("fib(35):", fibonacci(35));
    console.timeEnd("fib(35) 第一次");
    
    console.time("fib(35) 第二次（缓存）");
    console.log("fib(35):", fibonacci(35));
    console.timeEnd("fib(35) 第二次（缓存）");
    
    // 节流演示
    const throttledLog = throttle((msg: string) => {
        console.log("节流输出:", msg);
    }, 1000);
    
    throttledLog("消息1");  // 立即执行
    throttledLog("消息2");  // 被节流
    throttledLog("消息3");  // 被节流
    
    // 偏函数应用演示
    const add = (a: number, b: number, c: number): number => a + b + c;
    const add5 = partial(add, 5);
    console.log("add5(10, 15):", add5(10, 15));  // 30
    
    // 管道演示
    const result = pipe(
        5,
        x => x * 2,      // 10
        x => x + 3,      // 13
        x => x.toString() // "13"
    );
    console.log("管道结果:", result);
}

demonstrateHigherOrderFunctions();

// ============================================
// 2. 函数组合
// ============================================

// 组合函数（从右到左）
function compose<T>(...fns: Array<(x: T) => T>): (x: T) => T {
    return (x: T): T => fns.reduceRight((acc, fn) => fn(acc), x);
}

// 管道函数（从左到右）
function flow<T>(...fns: Array<(x: T) => T>): (x: T) => T {
    return (x: T): T => fns.reduce((acc, fn) => fn(acc), x);
}

// 通用组合（支持类型转换）
function composeAll<T>(...fns: T[]): T extends (arg: infer A) => infer B ? (arg: A) => B : never {
    return ((x: any) => fns.reduceRight((acc, fn: any) => fn(acc), x)) as any;
}

// 实用函数
const add = (n: number) => (x: number): number => x + n;
const multiply = (n: number) => (x: number): number => x * n;
const toString = (x: number): string => x.toString();
const split = (sep: string) => (str: string): string[] => str.split(sep);
const join = (sep: string) => (arr: string[]): string => arr.join(sep);
const map = <T, U>(fn: (x: T) => U) => (arr: T[]): U[] => arr.map(fn);
const filter = <T>(predicate: (x: T) => boolean) => (arr: T[]): T[] => arr.filter(predicate);
const reduce = <T, U>(fn: (acc: U, x: T) => U, initial: U) => (arr: T[]): U => arr.reduce(fn, initial);

// 演示函数组合
function demonstrateFunctionComposition() {
    console.log("\n=== 函数组合演示 ===");
    
    // 从右到左组合
    const composed = compose(
        add(10),
        multiply(2),
        add(5)
    );
    // 计算: add(5) -> multiply(2) -> add(10)
    // 100 -> 105 -> 210 -> 220
    console.log("compose结果 (100):", composed(100));  // 220
    
    // 从左到右组合（flow）
    const flowed = flow(
        add(10),
        multiply(2),
        add(5)
    );
    // 计算: add(10) -> multiply(2) -> add(5)
    // 100 -> 110 -> 220 -> 225
    console.log("flow结果 (100):", flowed(100));  // 225
    
    // 复杂组合：数据处理管道
    const processData = flow(
        filter((x: number) => x > 0),
        map((x: number) => x * 2),
        filter((x: number) => x > 10),
        reduce((acc: number, x: number) => acc + x, 0)
    );
    
    const data = [-5, 3, 8, -2, 10, 1, 15];
    console.log("原始数据:", data);
    console.log("处理后:", processData(data));  // (3*2) + (8*2) + (10*2) + (15*2) = 72
    
    // 字符串处理组合
    const processString = flow(
        (s: string) => s.toLowerCase(),
        split(" "),
        filter((s: string) => s.length > 3),
        map((s: string) => s.charAt(0).toUpperCase() + s.slice(1)),
        join(" ")
    );
    
    const sentence = "The quick brown fox jumps over the lazy dog";
    console.log("原始句子:", sentence);
    console.log("处理后:", processString(sentence));
}

demonstrateFunctionComposition();

// ============================================
// 3. 柯里化
// ============================================

// 自动柯里化
type Curried<T> = T extends (arg: infer A, ...args: infer R) => infer Ret
    ? R extends [any, ...any[]]
        ? (arg: A) => Curried<(...args: R) => Ret>
        : T
    : T;

function curry<T extends (...args: any[]) => any>(fn: T): Curried<T> {
    return function curried(...args: any[]): any {
        if (args.length >= fn.length) {
            return fn(...args);
        } else {
            return (...nextArgs: any[]) => curried(...args, ...nextArgs);
        }
    } as Curried<T>;
}

// 演示柯里化
function demonstrateCurrying() {
    console.log("\n=== 柯里化演示 ===");
    
    // 原始函数
    const addThree = (a: number, b: number, c: number): number => a + b + c;
    const curriedAddThree = curry(addThree);
    
    console.log("curriedAddThree(1)(2)(3):", curriedAddThree(1)(2)(3));
    console.log("curriedAddThree(1, 2)(3):", curriedAddThree(1, 2)(3));
    console.log("curriedAddThree(1)(2, 3):", curriedAddThree(1)(2, 3));
    
    // 实际应用：配置生成器
    const createURL = (protocol: string, domain: string, path: string): string => 
        `${protocol}://${domain}/${path}`;
    const curriedURL = curry(createURL);
    
    const httpsURL = curriedURL("https");
    const apiURL = httpsURL("api.example.com");
    const usersEndpoint = apiURL("users");
    const postsEndpoint = apiURL("posts");
    
    console.log("Users endpoint:", usersEndpoint);
    console.log("Posts endpoint:", postsEndpoint);
    
    // 数学运算柯里化
    const calculate = curry((op: string, a: number, b: number): number => {
        switch (op) {
            case 'add': return a + b;
            case 'subtract': return a - b;
            case 'multiply': return a * b;
            case 'divide': return a / b;
            default: throw new Error(`未知操作: ${op}`);
        }
    });
    
    const addOp = calculate('add');
    const multiplyOp = calculate('multiply');
    
    console.log("addOp(5, 3):", addOp(5, 3));
    console.log("multiplyOp(4, 7):", multiplyOp(4, 7));
}

demonstrateCurrying();

// ============================================
// 4. Monad模式
// ============================================

// Maybe Monad（处理可能的空值）
class Maybe<T> {
    private constructor(private value: T | null) {}
    
    static of<T>(value: T | null): Maybe<T> {
        return new Maybe(value);
    }
    
    static just<T>(value: T): Maybe<T> {
        return new Maybe(value);
    }
    
    static nothing<T>(): Maybe<T> {
        return new Maybe<T>(null);
    }
    
    isNothing(): boolean {
        return this.value === null || this.value === undefined;
    }
    
    isJust(): boolean {
        return !this.isNothing();
    }
    
    map<U>(fn: (value: T) => U): Maybe<U> {
        return this.isNothing() 
            ? Maybe.nothing<U>() 
            : Maybe.just(fn(this.value!));
    }
    
    flatMap<U>(fn: (value: T) => Maybe<U>): Maybe<U> {
        return this.isNothing() 
            ? Maybe.nothing<U>() 
            : fn(this.value!);
    }
    
    filter(predicate: (value: T) => boolean): Maybe<T> {
        return this.isNothing() || predicate(this.value!)
            ? this
            : Maybe.nothing<T>();
    }
    
    getOrElse(defaultValue: T): T {
        return this.isNothing() ? defaultValue : this.value!;
    }
    
    getOrElseThrow(error: Error): T {
        if (this.isNothing()) throw error;
        return this.value!;
    }
    
    orElse(alternative: Maybe<T>): Maybe<T> {
        return this.isNothing() ? alternative : this;
    }
    
    tap(fn: (value: T) => void): Maybe<T> {
        if (this.isJust()) fn(this.value!);
        return this;
    }
    
    toString(): string {
        return this.isNothing() ? 'Nothing' : `Just(${this.value})`;
    }
}

// Either Monad（处理错误）
type Either<L, R> = Left<L, R> | Right<L, R>;

class Left<L, R> {
    readonly _tag = 'Left';
    constructor(readonly value: L) {}
    
    map<U>(_fn: (value: R) => U): Either<L, U> {
        return new Left<L, U>(this.value);
    }
    
    flatMap<U>(_fn: (value: R) => Either<L, U>): Either<L, U> {
        return new Left<L, U>(this.value);
    }
    
    fold<T>(leftFn: (left: L) => T, _rightFn: (right: R) => T): T {
        return leftFn(this.value);
    }
    
    isLeft(): this is Left<L, R> { return true; }
    isRight(): this is Right<L, R> { return false; }
}

class Right<L, R> {
    readonly _tag = 'Right';
    constructor(readonly value: R) {}
    
    map<U>(fn: (value: R) => U): Either<L, U> {
        return new Right<L, U>(fn(this.value));
    }
    
    flatMap<U>(fn: (value: R) => Either<L, U>): Either<L, U> {
        return fn(this.value);
    }
    
    fold<T>(_leftFn: (left: L) => T, rightFn: (right: R) => T): T {
        return rightFn(this.value);
    }
    
    isLeft(): this is Left<L, R> { return false; }
    isRight(): this is Right<L, R> { return true; }
}

const Either = {
    left: <L, R>(value: L): Either<L, R> => new Left(value),
    right: <L, R>(value: R): Either<L, R> => new Right(value),
    
    // 尝试执行，捕获异常转为Left
    tryCatch: <L, R>(fn: () => R, onError: (error: any) => L): Either<L, R> => {
        try {
            return new Right(fn());
        } catch (e) {
            return new Left(onError(e));
        }
    }
};

// IO Monad（延迟副作用）
class IO<T> {
    constructor(private effect: () => T) {}
    
    static of<T>(value: T): IO<T> {
        return new IO(() => value);
    }
    
    static fromEffect<T>(effect: () => T): IO<T> {
        return new IO(effect);
    }
    
    map<U>(fn: (value: T) => U): IO<U> {
        return new IO(() => fn(this.effect()));
    }
    
    flatMap<U>(fn: (value: T) => IO<U>): IO<U> {
        return new IO(() => fn(this.effect()).run());
    }
    
    tap(fn: (value: T) => void): IO<T> {
        return new IO(() => {
            const result = this.effect();
            fn(result);
            return result;
        });
    }
    
    run(): T {
        return this.effect();
    }
}

// 演示Monad模式
function demonstrateMonads() {
    console.log("\n=== Monad模式演示 ===");
    
    // Maybe Monad 演示
    console.log("\n--- Maybe Monad ---");
    
    const maybeValue = Maybe.of(10)
        .map(x => x * 2)
        .map(x => x + 5);
    console.log("Maybe value:", maybeValue.toString());
    console.log("Value or 0:", maybeValue.getOrElse(0));
    
    const nothingValue = Maybe.of<number>(null)
        .map(x => x * 2);
    console.log("Nothing value:", nothingValue.toString());
    console.log("Nothing or 100:", nothingValue.getOrElse(100));
    
    // 链式安全操作
    interface User {
        name: string;
        address?: {
            city?: string;
        };
    }
    
    const user: User | null = {
        name: "Alice",
        address: {
            city: "New York"
        }
    };
    
    const city = Maybe.of(user)
        .map(u => u.address)
        .map(a => a?.city)
        .getOrElse("Unknown");
    
    console.log("City:", city);
    
    // Either Monad 演示
    console.log("\n--- Either Monad ---");
    
    function divide(a: number, b: number): Either<string, number> {
        return b === 0 
            ? Either.left("除数不能为零")
            : Either.right(a / b);
    }
    
    function sqrt(n: number): Either<string, number> {
        return n < 0 
            ? Either.left("负数没有实数平方根")
            : Either.right(Math.sqrt(n));
    }
    
    const result1 = divide(10, 2)
        .flatMap(x => divide(x, 5));
    
    console.log("10/2/5 =", result1.fold(
        err => `错误: ${err}`,
        val => `结果: ${val}`
    ));
    
    const result2 = divide(10, 0);
    console.log("10/0 =", result2.fold(
        err => `错误: ${err}`,
        val => `结果: ${val}`
    ));
    
    // 链式错误处理
    const complexCalc = divide(100, 4)
        .flatMap(x => divide(x, 5))
        .flatMap(sqrt);
    
    console.log("sqrt(100/4/5) =", complexCalc.fold(
        err => `错误: ${err}`,
        val => `结果: ${val}`
    ));
    
    // tryCatch
    const parsed = Either.tryCatch(
        () => JSON.parse('{"name": "Bob"}'),
        e => `解析错误: ${e}`
    );
    
    console.log("JSON解析:", parsed.fold(
        err => err,
        val => `成功: ${JSON.stringify(val)}`
    ));
    
    // IO Monad 演示
    console.log("\n--- IO Monad ---");
    
    const readLine = IO.fromEffect(() => "模拟用户输入");
    const writeLine = (msg: string) => IO.fromEffect(() => {
        console.log(msg);
        return undefined;
    });
    
    const program = readLine
        .map(input => input.toUpperCase())
        .flatMap(processed => writeLine(`处理后的输入: ${processed}`));
    
    console.log("IO程序已定义（尚未执行）");
    program.run();
}

demonstrateMonads();

// ============================================
// 5. 透镜（Lens）模式
// ============================================

// 透镜：函数式地操作嵌套数据结构
type Lens<S, A> = {
    get: (s: S) => A;
    set: (a: A) => (s: S) => S;
    modify: (fn: (a: A) => A) => (s: S) => S;
};

function createLens<S, A>(get: (s: S) => A, set: (a: A) => (s: S) => S): Lens<S, A> {
    return {
        get,
        set,
        modify: (fn) => (s) => set(fn(get(s)))(s)
    };
}

// 组合透镜
type LensComposer = <S, A, B>(
    lens1: Lens<S, A>,
    lens2: Lens<A, B>
) => Lens<S, B>;

const composeLenses: LensComposer = (lens1, lens2) => ({
    get: (s) => lens2.get(lens1.get(s)),
    set: (b) => (s) => lens1.modify(lens2.set(b))(s),
    modify: (fn) => (s) => lens1.modify(lens2.modify(fn))(s)
});

// 演示透镜
function demonstrateLenses() {
    console.log("\n=== 透镜模式演示 ===");
    
    interface Address {
        street: string;
        city: string;
        zipCode: string;
    }
    
    interface Person {
        name: string;
        age: number;
        address: Address;
    }
    
    const person: Person = {
        name: "Alice",
        age: 30,
        address: {
            street: "123 Main St",
            city: "New York",
            zipCode: "10001"
        }
    };
    
    // 创建透镜
    const nameLens = createLens<Person, string>(
        p => p.name,
        name => p => ({ ...p, name })
    );
    
    const addressLens = createLens<Person, Address>(
        p => p.address,
        address => p => ({ ...p, address })
    );
    
    const cityLens = createLens<Address, string>(
        a => a.city,
        city => a => ({ ...a, city })
    );
    
    // 组合透镜
    const personCityLens = composeLenses(addressLens, cityLens);
    
    console.log("原始城市:", personCityLens.get(person));
    
    const updatedPerson = personCityLens.set("Los Angeles")(person);
    console.log("更新后的城市:", updatedPerson.address.city);
    
    // 使用modify
    const agedPerson = createLens<Person, number>(
        p => p.age,
        age => p => ({ ...p, age })
    ).modify(age => age + 1)(person);
    
    console.log("原始年龄:", person.age);
    console.log("增加后年龄:", agedPerson.age);
}

demonstrateLenses();

console.log("\n========================================");
console.log("TypeScript 函数式工具演示完成");
console.log("========================================");
