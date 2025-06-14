# 形式语言理论应用实例 (Formal Language Theory Application Examples)

## 目录

1. [引言](#引言)
2. [编译器设计](#编译器设计)
3. [正则表达式引擎](#正则表达式引擎)
4. [语法分析器](#语法分析器)
5. [代码生成器](#代码生成器)
6. [程序验证](#程序验证)
7. [自然语言处理](#自然语言处理)
8. [总结](#总结)

## 交叉引用与关联

### 相关理论领域

- **[自动机理论](01_Automata_Theory.md)**：状态机实现
- **[语言层次结构](02_Language_Hierarchy.md)**：语言分类与能力
- **[语义理论](03_Semantics_Theory.md)**：语义分析与解释
- **[语法理论](04_Syntax_Theory.md)**：语法分析与生成
- **[计算理论](05_Computation_Theory.md)**：计算复杂度分析

### 基础依赖关系

- **[逻辑基础](../01_Foundational_Theory/01_Logic_Foundation.md)**：形式化推理
- **[类型理论](../02_Type_Theory/01_Basic_Type_Theory.md)**：类型检查与推导
- **[时态逻辑](../06_Temporal_Logic/01_Temporal_Logic_Foundation.md)**：程序性质验证

## 引言

本章节展示形式语言理论在实际编程语言和工具中的应用。从编译器设计到正则表达式引擎，形式语言理论为现代软件开发提供了理论基础。

## 编译器设计

### 2.1 词法分析器

**有限状态自动机实现**：
词法分析器使用DFA识别词法单元。

**定义 2.1.1 (词法分析器)**
词法分析器是一个五元组 $LA = (Q, \Sigma, \delta, q_0, F)$，其中：

- $Q$ 是状态集合
- $\Sigma$ 是输入字母表
- $\delta: Q \times \Sigma \rightarrow Q$ 是转移函数
- $q_0 \in Q$ 是初始状态
- $F \subseteq Q$ 是接受状态集合

-**算法 2.1.1 (词法分析算法)**

```python
class LexicalAnalyzer:
    def __init__(self):
        self.dfa = self.build_dfa()
        self.current_state = self.dfa.initial_state
        self.buffer = ""
    
    def tokenize(self, source_code):
        tokens = []
        i = 0
        
        while i < len(source_code):
            char = source_code[i]
            
            # 尝试转移
            next_state = self.dfa.transition(self.current_state, char)
            
            if next_state is None:
                # 无法转移，生成token
                if self.current_state in self.dfa.accepting_states:
                    token = self.create_token(self.buffer, self.current_state)
                    tokens.append(token)
                
                # 重置状态
                self.current_state = self.dfa.initial_state
                self.buffer = ""
            else:
                # 成功转移
                self.current_state = next_state
                self.buffer += char
                i += 1
        
        return tokens
    
    def create_token(self, lexeme, state):
        token_type = self.get_token_type(state)
        return Token(token_type, lexeme)
```

**正则表达式到DFA转换**：

```python
def regex_to_dfa(regex):
    # 1. 构建NFA
    nfa = build_nfa_from_regex(regex)
    
    # 2. 子集构造法转换为DFA
    dfa = subset_construction(nfa)
    
    # 3. 最小化DFA
    minimized_dfa = minimize_dfa(dfa)
    
    return minimized_dfa

def subset_construction(nfa):
    dfa_states = set()
    dfa_transitions = {}
    dfa_accepting = set()
    
    # 初始状态：ε闭包
    initial_state = epsilon_closure(nfa, {nfa.initial_state})
    dfa_states.add(frozenset(initial_state))
    
    # 广度优先搜索构建DFA
    queue = [frozenset(initial_state)]
    processed = set()
    
    while queue:
        current_dfa_state = queue.pop(0)
        if current_dfa_state in processed:
            continue
        
        processed.add(current_dfa_state)
        
        # 对每个输入符号计算转移
        for symbol in nfa.alphabet:
            next_nfa_states = set()
            
            for nfa_state in current_dfa_state:
                if symbol in nfa.transitions.get(nfa_state, {}):
                    next_nfa_states.update(nfa.transitions[nfa_state][symbol])
            
            if next_nfa_states:
                next_dfa_state = epsilon_closure(nfa, next_nfa_states)
                dfa_states.add(frozenset(next_dfa_state))
                dfa_transitions[(current_dfa_state, symbol)] = frozenset(next_dfa_state)
                
                if next_dfa_state not in processed:
                    queue.append(frozenset(next_dfa_state))
    
    return DFA(dfa_states, dfa_transitions, frozenset(initial_state), dfa_accepting)
```

### 2.2 语法分析器

**递归下降解析器**：
实现LL(1)语法分析器。

**定义 2.2.1 (LL(1)语法)**
文法 $G$ 是LL(1)的，如果对于每个产生式 $A \rightarrow \alpha \mid \beta$，有：
$$FIRST(\alpha) \cap FIRST(\beta) = \emptyset$$

-**算法 2.2.1 (递归下降解析器)**

```python
class RecursiveDescentParser:
    def __init__(self, grammar):
        self.grammar = grammar
        self.first_sets = self.compute_first_sets()
        self.follow_sets = self.compute_follow_sets()
        self.parsing_table = self.build_parsing_table()
    
    def parse(self, tokens):
        self.tokens = tokens
        self.current = 0
        return self.parse_expression()
    
    def parse_expression(self):
        # E -> T E'
        left = self.parse_term()
        return self.parse_expression_prime(left)
    
    def parse_expression_prime(self, left):
        # E' -> + T E' | ε
        if self.current < len(self.tokens) and self.tokens[self.current].type == 'PLUS':
            self.match('PLUS')
            right = self.parse_term()
            return self.parse_expression_prime(BinaryOp('+', left, right))
        else:
            return left
    
    def parse_term(self):
        # T -> F T'
        left = self.parse_factor()
        return self.parse_term_prime(left)
    
    def parse_term_prime(self, left):
        # T' -> * F T' | ε
        if self.current < len(self.tokens) and self.tokens[self.current].type == 'MULTIPLY':
            self.match('MULTIPLY')
            right = self.parse_factor()
            return self.parse_term_prime(BinaryOp('*', left, right))
        else:
            return left
    
    def parse_factor(self):
        # F -> ( E ) | NUMBER
        if self.current < len(self.tokens):
            if self.tokens[self.current].type == 'LPAREN':
                self.match('LPAREN')
                expr = self.parse_expression()
                self.match('RPAREN')
                return expr
            elif self.tokens[self.current].type == 'NUMBER':
                value = self.tokens[self.current].value
                self.match('NUMBER')
                return Number(value)
        
        raise SyntaxError("Unexpected token")
    
    def match(self, expected_type):
        if self.current < len(self.tokens) and self.tokens[self.current].type == expected_type:
            self.current += 1
        else:
            raise SyntaxError(f"Expected {expected_type}, got {self.tokens[self.current].type}")
```

**LR(1)解析器**：
实现自底向上的语法分析。

-**算法 2.2.2 (LR(1)解析器)**

```python
class LR1Parser:
    def __init__(self, grammar):
        self.grammar = grammar
        self.action_table = self.build_action_table()
        self.goto_table = self.build_goto_table()
    
    def parse(self, tokens):
        stack = [0]  # 状态栈
        symbols = []  # 符号栈
        tokens.append(Token('EOF', None))  # 添加结束标记
        
        i = 0
        while True:
            state = stack[-1]
            token = tokens[i]
            
            action = self.action_table.get((state, token.type))
            
            if action is None:
                raise SyntaxError(f"No action for state {state} and token {token.type}")
            
            if action.startswith('shift'):
                # 移进
                next_state = int(action.split()[1])
                stack.append(next_state)
                symbols.append(token)
                i += 1
            
            elif action.startswith('reduce'):
                # 归约
                production = int(action.split()[1])
                lhs, rhs = self.grammar.productions[production]
                
                # 弹出|rhs|个符号
                for _ in range(len(rhs)):
                    stack.pop()
                    symbols.pop()
                
                # 压入归约后的符号
                current_state = stack[-1]
                goto_state = self.goto_table.get((current_state, lhs))
                if goto_state is None:
                    raise SyntaxError(f"No goto for state {current_state} and symbol {lhs}")
                
                stack.append(goto_state)
                symbols.append(lhs)
            
            elif action == 'accept':
                # 接受
                return symbols[-1]
            
            else:
                raise SyntaxError(f"Invalid action: {action}")
```

## 正则表达式引擎

### 3.1 正则表达式匹配

**Thompson构造法**：
将正则表达式转换为NFA。

-**算法 3.1.1 (Thompson构造法)**

```python
def thompson_construction(regex):
    """将正则表达式转换为NFA"""
    postfix = infix_to_postfix(regex)
    stack = []
    
    for char in postfix:
        if char.isalnum():
            # 基本字符
            nfa = create_basic_nfa(char)
            stack.append(nfa)
        
        elif char == '.':
            # 连接
            nfa2 = stack.pop()
            nfa1 = stack.pop()
            nfa = concatenate_nfa(nfa1, nfa2)
            stack.append(nfa)
        
        elif char == '|':
            # 选择
            nfa2 = stack.pop()
            nfa1 = stack.pop()
            nfa = union_nfa(nfa1, nfa2)
            stack.append(nfa)
        
        elif char == '*':
            # 闭包
            nfa = stack.pop()
            nfa = kleene_star_nfa(nfa)
            stack.append(nfa)
    
    return stack[0]

def create_basic_nfa(char):
    """创建基本字符的NFA"""
    nfa = NFA()
    start_state = nfa.add_state()
    end_state = nfa.add_state()
    
    nfa.add_transition(start_state, char, end_state)
    nfa.set_initial_state(start_state)
    nfa.add_accepting_state(end_state)
    
    return nfa

def concatenate_nfa(nfa1, nfa2):
    """连接两个NFA"""
    nfa = NFA()
    
    # 复制nfa1的状态
    state_map1 = {}
    for state in nfa1.states:
        new_state = nfa.add_state()
        state_map1[state] = new_state
    
    # 复制nfa2的状态
    state_map2 = {}
    for state in nfa2.states:
        new_state = nfa.add_state()
        state_map2[state] = new_state
    
    # 复制转移
    for state, transitions in nfa1.transitions.items():
        for symbol, next_states in transitions.items():
            for next_state in next_states:
                nfa.add_transition(state_map1[state], symbol, state_map1[next_state])
    
    for state, transitions in nfa2.transitions.items():
        for symbol, next_states in transitions.items():
            for next_state in next_states:
                nfa.add_transition(state_map2[state], symbol, state_map2[next_state])
    
    # 连接：nfa1的接受状态到nfa2的初始状态的ε转移
    for accepting_state in nfa1.accepting_states:
        nfa.add_transition(state_map1[accepting_state], 'ε', state_map2[nfa2.initial_state])
    
    # 设置初始和接受状态
    nfa.set_initial_state(state_map1[nfa1.initial_state])
    for accepting_state in nfa2.accepting_states:
        nfa.add_accepting_state(state_map2[accepting_state])
    
    return nfa
```

### 3.2 正则表达式优化

**DFA最小化**：
使用Hopcroft算法最小化DFA。

-**算法 3.2.1 (Hopcroft算法)**

```python
def hopcroft_minimization(dfa):
    """使用Hopcroft算法最小化DFA"""
    # 初始分区：接受状态和非接受状态
    partition = [set(dfa.accepting_states), set(dfa.states - dfa.accepting_states)]
    partition = [p for p in partition if p]  # 移除空集
    
    # 工作列表：包含需要进一步分割的集合
    worklist = [p for p in partition if len(p) > 1]
    
    while worklist:
        current_set = worklist.pop(0)
        
        # 对每个输入符号尝试分割
        for symbol in dfa.alphabet:
            # 计算preimage
            preimage = set()
            for state in current_set:
                for prev_state, prev_symbol, next_state in dfa.transitions:
                    if prev_symbol == symbol and next_state == state:
                        preimage.add(prev_state)
            
            # 尝试分割当前集合
            new_partition = []
            for p in partition:
                intersection = p & preimage
                difference = p - preimage
                
                if intersection and difference:
                    new_partition.extend([intersection, difference])
                    if p in worklist:
                        worklist.remove(p)
                    if len(intersection) > 1:
                        worklist.append(intersection)
                    if len(difference) > 1:
                        worklist.append(difference)
                else:
                    new_partition.append(p)
            
            partition = new_partition
    
    # 构建最小化DFA
    minimized_dfa = build_minimized_dfa(dfa, partition)
    return minimized_dfa
```

## 语法分析器

### 4.1 抽象语法树构建

**AST节点定义**：

```python
class ASTNode:
    def __init__(self, node_type):
        self.node_type = node_type
        self.children = []
    
    def add_child(self, child):
        self.children.append(child)
    
    def accept(self, visitor):
        return visitor.visit(self)

class BinaryOp(ASTNode):
    def __init__(self, operator, left, right):
        super().__init__('BinaryOp')
        self.operator = operator
        self.left = left
        self.right = right
    
    def accept(self, visitor):
        return visitor.visit_binary_op(self)

class UnaryOp(ASTNode):
    def __init__(self, operator, operand):
        super().__init__('UnaryOp')
        self.operator = operator
        self.operand = operand
    
    def accept(self, visitor):
        return visitor.visit_unary_op(self)

class Variable(ASTNode):
    def __init__(self, name):
        super().__init__('Variable')
        self.name = name
    
    def accept(self, visitor):
        return visitor.visit_variable(self)

class Number(ASTNode):
    def __init__(self, value):
        super().__init__('Number')
        self.value = value
    
    def accept(self, visitor):
        return visitor.visit_number(self)
```

**访问者模式**：

```python
class ASTVisitor:
    def visit(self, node):
        method_name = f'visit_{node.node_type.lower()}'
        method = getattr(self, method_name, self.generic_visit)
        return method(node)
    
    def generic_visit(self, node):
        for child in node.children:
            child.accept(self)
    
    def visit_binary_op(self, node):
        node.left.accept(self)
        node.right.accept(self)
    
    def visit_unary_op(self, node):
        node.operand.accept(self)
    
    def visit_variable(self, node):
        pass
    
    def visit_number(self, node):
        pass

class TypeChecker(ASTVisitor):
    def __init__(self):
        self.symbol_table = {}
    
    def visit_binary_op(self, node):
        left_type = node.left.accept(self)
        right_type = node.right.accept(self)
        
        # 类型检查规则
        if node.operator in ['+', '-', '*', '/']:
            if left_type == 'int' and right_type == 'int':
                return 'int'
            elif left_type == 'float' and right_type in ['int', 'float']:
                return 'float'
            else:
                raise TypeError(f"Cannot apply {node.operator} to {left_type} and {right_type}")
        
        elif node.operator in ['==', '!=', '<', '>', '<=', '>=']:
            if left_type == right_type:
                return 'bool'
            else:
                raise TypeError(f"Cannot compare {left_type} and {right_type}")
        
        elif node.operator in ['&&', '||']:
            if left_type == 'bool' and right_type == 'bool':
                return 'bool'
            else:
                raise TypeError(f"Cannot apply {node.operator} to {left_type} and {right_type}")
    
    def visit_variable(self, node):
        if node.name in self.symbol_table:
            return self.symbol_table[node.name]
        else:
            raise NameError(f"Undefined variable {node.name}")
    
    def visit_number(self, node):
        if isinstance(node.value, int):
            return 'int'
        elif isinstance(node.value, float):
            return 'float'
        else:
            return 'unknown'
```

## 代码生成器

### 5.1 三地址代码生成

**三地址代码格式**：

```python
class ThreeAddressCode:
    def __init__(self, op, arg1=None, arg2=None, result=None):
        self.op = op
        self.arg1 = arg1
        self.arg2 = arg2
        self.result = result
    
    def __str__(self):
        if self.op == 'assign':
            return f"{self.result} = {self.arg1}"
        elif self.op in ['add', 'sub', 'mul', 'div']:
            return f"{self.result} = {self.arg1} {self.op} {self.arg2}"
        elif self.op == 'label':
            return f"{self.result}:"
        elif self.op == 'goto':
            return f"goto {self.result}"
        elif self.op in ['if_false', 'if_true']:
            return f"if {self.arg1} {self.op} goto {self.result}"
        else:
            return f"{self.op} {self.arg1} {self.arg2} {self.result}"

class CodeGenerator(ASTVisitor):
    def __init__(self):
        self.code = []
        self.temp_counter = 0
        self.label_counter = 0
    
    def new_temp(self):
        temp = f"t{self.temp_counter}"
        self.temp_counter += 1
        return temp
    
    def new_label(self):
        label = f"L{self.label_counter}"
        self.label_counter += 1
        return label
    
    def visit_binary_op(self, node):
        # 生成左操作数代码
        left_temp = node.left.accept(self)
        
        # 生成右操作数代码
        right_temp = node.right.accept(self)
        
        # 生成操作代码
        result_temp = self.new_temp()
        
        if node.operator == '+':
            self.code.append(ThreeAddressCode('add', left_temp, right_temp, result_temp))
        elif node.operator == '-':
            self.code.append(ThreeAddressCode('sub', left_temp, right_temp, result_temp))
        elif node.operator == '*':
            self.code.append(ThreeAddressCode('mul', left_temp, right_temp, result_temp))
        elif node.operator == '/':
            self.code.append(ThreeAddressCode('div', left_temp, right_temp, result_temp))
        elif node.operator == '==':
            self.code.append(ThreeAddressCode('eq', left_temp, right_temp, result_temp))
        elif node.operator == '!=':
            self.code.append(ThreeAddressCode('ne', left_temp, right_temp, result_temp))
        elif node.operator == '<':
            self.code.append(ThreeAddressCode('lt', left_temp, right_temp, result_temp))
        elif node.operator == '>':
            self.code.append(ThreeAddressCode('gt', left_temp, right_temp, result_temp))
        elif node.operator == '<=':
            self.code.append(ThreeAddressCode('le', left_temp, right_temp, result_temp))
        elif node.operator == '>=':
            self.code.append(ThreeAddressCode('ge', left_temp, right_temp, result_temp))
        
        return result_temp
    
    def visit_variable(self, node):
        return node.name
    
    def visit_number(self, node):
        return str(node.value)
```

### 5.2 目标代码生成

**x86汇编代码生成**：

```python
class X86CodeGenerator:
    def __init__(self):
        self.code = []
        self.data_section = []
        self.symbol_table = {}
        self.stack_offset = 0
    
    def generate_prologue(self, function_name):
        self.code.extend([
            f"    .globl {function_name}",
            f"{function_name}:",
            "    pushq %rbp",
            "    movq %rsp, %rbp",
            "    subq $16, %rsp"  # 分配栈空间
        ])
    
    def generate_epilogue(self):
        self.code.extend([
            "    movq %rbp, %rsp",
            "    popq %rbp",
            "    ret"
        ])
    
    def generate_arithmetic(self, op, left_reg, right_reg, result_reg):
        if op == '+':
            self.code.append(f"    addq {right_reg}, {left_reg}")
            self.code.append(f"    movq {left_reg}, {result_reg}")
        elif op == '-':
            self.code.append(f"    subq {right_reg}, {left_reg}")
            self.code.append(f"    movq {left_reg}, {result_reg}")
        elif op == '*':
            self.code.append(f"    imulq {right_reg}, {left_reg}")
            self.code.append(f"    movq {left_reg}, {result_reg}")
        elif op == '/':
            self.code.append(f"    movq {left_reg}, %rax")
            self.code.append(f"    cqto")
            self.code.append(f"    idivq {right_reg}")
            self.code.append(f"    movq %rax, {result_reg}")
    
    def generate_comparison(self, op, left_reg, right_reg, result_reg):
        self.code.append(f"    cmpq {right_reg}, {left_reg}")
        
        if op == '==':
            self.code.append(f"    sete %al")
        elif op == '!=':
            self.code.append(f"    setne %al")
        elif op == '<':
            self.code.append(f"    setl %al")
        elif op == '>':
            self.code.append(f"    setg %al")
        elif op == '<=':
            self.code.append(f"    setle %al")
        elif op == '>=':
            self.code.append(f"    setge %al")
        
        self.code.append(f"    movzbq %al, {result_reg}")
    
    def generate_assignment(self, var_name, value_reg):
        if var_name in self.symbol_table:
            offset = self.symbol_table[var_name]
            self.code.append(f"    movq {value_reg}, -{offset}(%rbp)")
        else:
            # 新变量，分配栈空间
            self.stack_offset += 8
            self.symbol_table[var_name] = self.stack_offset
            self.code.append(f"    movq {value_reg}, -{self.stack_offset}(%rbp)")
    
    def generate_variable_load(self, var_name, target_reg):
        if var_name in self.symbol_table:
            offset = self.symbol_table[var_name]
            self.code.append(f"    movq -{offset}(%rbp), {target_reg}")
        else:
            raise NameError(f"Undefined variable {var_name}")
```

## 程序验证

### 6.1 静态分析

**数据流分析**：

```python
class DataFlowAnalysis:
    def __init__(self, cfg):
        self.cfg = cfg
        self.in_sets = {}
        self.out_sets = {}
    
    def analyze_liveness(self):
        """活跃变量分析"""
        # 初始化
        for node in self.cfg.nodes:
            self.in_sets[node] = set()
            self.out_sets[node] = set()
        
        # 迭代直到收敛
        changed = True
        while changed:
            changed = False
            
            for node in self.cfg.nodes:
                old_in = self.in_sets[node].copy()
                
                # 计算gen和kill集合
                gen = self.compute_gen_set(node)
                kill = self.compute_kill_set(node)
                
                # 计算out集合
                out = set()
                for successor in self.cfg.successors(node):
                    out.update(self.in_sets[successor])
                
                # 计算in集合
                self.in_sets[node] = gen.union(out - kill)
                
                if self.in_sets[node] != old_in:
                    changed = True
    
    def compute_gen_set(self, node):
        """计算gen集合：在节点中定义但在使用前未重新定义的变量"""
        gen = set()
        used = set()
        
        for instruction in reversed(node.instructions):
            # 检查使用
            for var in instruction.uses:
                if var not in used:
                    gen.add(var)
                    used.add(var)
            
            # 检查定义
            for var in instruction.defines:
                used.discard(var)
        
        return gen
    
    def compute_kill_set(self, node):
        """计算kill集合：在节点中定义的变量"""
        kill = set()
        
        for instruction in node.instructions:
            kill.update(instruction.defines)
        
        return kill
```

### 6.2 模型检查

**线性时态逻辑模型检查**：

```python
class LTLModelChecker:
    def __init__(self, model):
        self.model = model
    
    def check_formula(self, formula):
        """检查LTL公式在模型中的有效性"""
        # 构建Büchi自动机
        buchi_automaton = self.build_buchi_automaton(formula)
        
        # 构建乘积自动机
        product_automaton = self.build_product_automaton(
            self.model, buchi_automaton)
        
        # 检查接受循环
        return self.check_accepting_cycle(product_automaton)
    
    def build_buchi_automaton(self, formula):
        """将LTL公式转换为Büchi自动机"""
        # 使用LTL2BA算法
        automaton = BuchiAutomaton()
        
        # 构建状态
        states = self.generate_states(formula)
        
        # 构建转移
        transitions = self.generate_transitions(formula, states)
        
        # 设置接受条件
        accepting_states = self.generate_accepting_states(formula, states)
        
        automaton.set_states(states)
        automaton.set_transitions(transitions)
        automaton.set_accepting_states(accepting_states)
        
        return automaton
    
    def check_accepting_cycle(self, automaton):
        """检查自动机中是否存在接受循环"""
        # 使用嵌套深度优先搜索
        return self.nested_dfs(automaton)
    
    def nested_dfs(self, automaton):
        """嵌套深度优先搜索算法"""
        visited = set()
        accepting_visited = set()
        
        for state in automaton.states:
            if state not in visited:
                if self.dfs_cycle(state, automaton, visited, accepting_visited):
                    return True
        
        return False
    
    def dfs_cycle(self, state, automaton, visited, accepting_visited):
        """深度优先搜索寻找循环"""
        visited.add(state)
        
        for next_state in automaton.successors(state):
            if next_state not in visited:
                if self.dfs_cycle(next_state, automaton, visited, accepting_visited):
                    return True
            elif next_state in accepting_visited:
                # 找到接受循环
                return True
        
        if state in automaton.accepting_states:
            accepting_visited.add(state)
        
        return False
```

## 自然语言处理

### 7.1 句法分析

**依存句法分析**：

```python
class DependencyParser:
    def __init__(self):
        self.model = self.load_model()
    
    def parse(self, sentence):
        """解析句子的依存关系"""
        tokens = self.tokenize(sentence)
        features = self.extract_features(tokens)
        scores = self.model.predict(features)
        
        # 使用最大生成树算法
        tree = self.maximum_spanning_tree(scores)
        
        return self.build_dependencies(tokens, tree)
    
    def extract_features(self, tokens):
        """提取特征"""
        features = []
        
        for i, token in enumerate(tokens):
            # 词形特征
            word_features = [
                token.word,
                token.lemma,
                token.pos_tag,
                token.dep_tag
            ]
            
            # 上下文特征
            context_features = []
            for offset in [-2, -1, 1, 2]:
                if 0 <= i + offset < len(tokens):
                    context_features.extend([
                        tokens[i + offset].word,
                        tokens[i + offset].pos_tag
                    ])
                else:
                    context_features.extend(['<PAD>', '<PAD>'])
            
            # 组合特征
            combined_features = word_features + context_features
            features.append(combined_features)
        
        return features
    
    def maximum_spanning_tree(self, scores):
        """使用最大生成树算法构建依存树"""
        n = len(scores)
        
        # 使用Prim算法
        tree = [-1] * n  # 父节点数组
        key = [float('-inf')] * n  # 最大权重
        mst_set = [False] * n
        
        key[0] = 0  # 根节点
        
        for _ in range(n):
            # 找到最大权重的未访问节点
            u = max(range(n), key=lambda i: key[i] if not mst_set[i] else float('-inf'))
            mst_set[u] = True
            
            # 更新相邻节点的权重
            for v in range(n):
                if not mst_set[v] and scores[u][v] > key[v]:
                    key[v] = scores[u][v]
                    tree[v] = u
        
        return tree
```

### 7.2 语义分析

**语义角色标注**：

```python
class SemanticRoleLabeler:
    def __init__(self):
        self.model = self.load_model()
    
    def label_roles(self, sentence, predicates):
        """标注语义角色"""
        tokens = self.tokenize(sentence)
        roles = []
        
        for predicate in predicates:
            predicate_roles = self.label_predicate_roles(tokens, predicate)
            roles.extend(predicate_roles)
        
        return roles
    
    def label_predicate_roles(self, tokens, predicate):
        """标注单个谓词的语义角色"""
        features = self.extract_srl_features(tokens, predicate)
        scores = self.model.predict(features)
        
        # 使用维特比算法进行序列标注
        best_labels = self.viterbi_decode(scores)
        
        return self.build_roles(tokens, predicate, best_labels)
    
    def extract_srl_features(self, tokens, predicate):
        """提取语义角色标注特征"""
        features = []
        predicate_pos = predicate.position
        
        for i, token in enumerate(tokens):
            # 基本特征
            basic_features = [
                token.word,
                token.lemma,
                token.pos_tag,
                token.dep_tag
            ]
            
            # 谓词特征
            predicate_features = [
                tokens[predicate_pos].word,
                tokens[predicate_pos].lemma,
                tokens[predicate_pos].pos_tag
            ]
            
            # 位置特征
            position_features = [
                i - predicate_pos,  # 相对位置
                abs(i - predicate_pos)  # 绝对距离
            ]
            
            # 路径特征
            path_features = self.extract_path_features(tokens, i, predicate_pos)
            
            combined_features = (basic_features + predicate_features + 
                               position_features + path_features)
            features.append(combined_features)
        
        return features
    
    def viterbi_decode(self, scores):
        """维特比算法进行序列标注"""
        n, num_labels = scores.shape
        
        # 动态规划表
        dp = np.full((n, num_labels), float('-inf'))
        backpointer = np.zeros((n, num_labels), dtype=int)
        
        # 初始化
        dp[0] = scores[0]
        
        # 前向传播
        for t in range(1, n):
            for j in range(num_labels):
                for i in range(num_labels):
                    score = dp[t-1, i] + scores[t, j]
                    if score > dp[t, j]:
                        dp[t, j] = score
                        backpointer[t, j] = i
        
        # 回溯
        best_labels = []
        best_label = np.argmax(dp[-1])
        
        for t in range(n-1, -1, -1):
            best_labels.append(best_label)
            best_label = backpointer[t, best_label]
        
        return list(reversed(best_labels))
```

## 总结

本章节展示了形式语言理论在实际编程和自然语言处理中的应用。从编译器设计到程序验证，形式语言理论为软件开发提供了强大的理论基础。

### 关键要点

1. **理论指导实践**：自动机理论、语法理论等为工具开发提供理论基础
2. -**算法实现**：将形式化算法转化为实际可执行的代码
3. **性能优化**：通过算法优化提高工具性能
4. **正确性保证**：通过形式化方法保证工具的正确性

### 应用领域

1. **编译器技术**：词法分析、语法分析、代码生成
2. **文本处理**：正则表达式、模式匹配
3. **程序验证**：静态分析、模型检查
4. **自然语言处理**：句法分析、语义分析

### 未来趋势

1. **AI与形式语言融合**：机器学习在语言处理中的应用
2. **并行处理**：大规模文本的并行处理
3. **实时处理**：流式数据的实时分析
4. **多模态处理**：文本、语音、图像的联合处理

---

**相关文档**：

- [自动机理论](01_Automata_Theory.md)
- [语言层次结构](02_Language_Hierarchy.md)
- [语义理论](03_Semantics_Theory.md)
- [语法理论](04_Syntax_Theory.md)
- [计算理论](05_Computation_Theory.md)
