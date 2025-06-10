# 现代软件架构分析：从前端到后端的全栈视角

## 目录

- [现代软件架构分析：从前端到后端的全栈视角](#现代软件架构分析从前端到后端的全栈视角)
  - [目录](#目录)
  - [1. 引言](#1-引言)
    - [1.1 分析背景与目标](#11-分析背景与目标)
    - [1.2 技术生态现状概览](#12-技术生态现状概览)
  - [2. 前端架构](#2-前端架构)
    - [2.1 现代UI框架分析](#21-现代ui框架分析)
    - [2.2 状态管理演进](#22-状态管理演进)
    - [2.3 组件设计模式](#23-组件设计模式)
    - [2.4 构建与优化系统](#24-构建与优化系统)
  - [3. 后端架构](#3-后端架构)
    - [3.1 服务器框架比较](#31-服务器框架比较)
    - [3.2 API设计范式](#32-api设计范式)
    - [3.3 微服务与单体架构](#33-微服务与单体架构)
    - [3.4 函数即服务(FaaS)](#34-函数即服务faas)
  - [4. 数据存储与处理](#4-数据存储与处理)
    - [4.1 关系型数据库现状](#41-关系型数据库现状)
    - [4.2 NoSQL解决方案](#42-nosql解决方案)
    - [4.3 数据访问层模式](#43-数据访问层模式)
    - [4.4 缓存策略与实现](#44-缓存策略与实现)
  - [5. 全栈架构模式](#5-全栈架构模式)
    - [5.1 JAMStack架构](#51-jamstack架构)
    - [5.2 MERN/MEAN/PERN栈](#52-mernmeanpern栈)
    - [5.3 云原生应用架构](#53-云原生应用架构)
    - [5.4 服务网格与容器编排](#54-服务网格与容器编排)
  - [6. 热门开源项目架构分析](#6-热门开源项目架构分析)
    - [6.1 VSCode架构解析](#61-vscode架构解析)
    - [6.2 Next.js内部架构](#62-nextjs内部架构)
    - [6.3 Redis核心设计](#63-redis核心设计)
    - [6.4 Kubernetes架构原理](#64-kubernetes架构原理)
  - [7. 新兴架构趋势](#7-新兴架构趋势)
    - [7.1 AI驱动的软件架构](#71-ai驱动的软件架构)
    - [7.2 WebAssembly应用架构](#72-webassembly应用架构)
    - [7.3 边缘计算模式](#73-边缘计算模式)
  - [8. 软件架构思维导图](#8-软件架构思维导图)
  - [9. 总结](#9-总结)

## 1. 引言

### 1.1 分析背景与目标

现代软件架构正经历前所未有的快速变革。本分析旨在提供从前端到后端的全栈视角，深入剖析当前热门技术栈、框架及应用架构的优缺点，帮助开发者和架构师做出更明智的技术决策。

### 1.2 技术生态现状概览

当前技术生态呈现多元化与专业化并存的特点。前端领域已从简单的DOM操作发展为复杂的应用平台；后端架构从单体应用向微服务与无服务器架构转变；数据存储也从传统关系型数据库扩展到多样化的存储解决方案。这种多样性带来了空前的灵活性，同时也增加了技术选型的复杂性。

## 2. 前端架构

### 2.1 现代UI框架分析

-**React生态系统**

React已成为前端开发的主导框架之一，其核心架构基于以下几个关键概念：

```jsx
// React组件示例 - 函数式组件与Hooks
function UserProfile({ userId }) {
  // 状态管理
  const [user, setUser] = useState(null);
  const [loading, setLoading] = useState(true);
  
  // 副作用处理
  useEffect(() => {
    async function loadUser() {
      setLoading(true);
      const data = await fetchUser(userId);
      setUser(data);
      setLoading(false);
    }
    loadUser();
  }, [userId]);
  
  if (loading) return <Spinner />;
  if (!user) return <ErrorMessage />;
  
  return (
    <div className="user-profile">
      <h1>{user.name}</h1>
      <UserStats stats={user.stats} />
      <UserActivity activities={user.activities} />
    </div>
  );
}
```

**React架构特点**：

- 虚拟DOM实现高效UI更新
- 单向数据流提高可预测性
- 组件化促进代码复用
- JSX实现声明式UI编程
- Hooks模式统一状态与生命周期逻辑

-**Vue.js架构**

Vue提供了更完整的框架体验，同时保持轻量级特性：

```vue
<!-- Vue组件示例 - 单文件组件 -->
<template>
  <div class="user-profile" v-if="!loading">
    <h1>{{ user.name }}</h1>
    <UserStats :stats="user.stats" />
    <UserActivity :activities="user.activities" />
  </div>
  <Spinner v-else />
</template>

<script>
export default {
  components: { UserStats, UserActivity, Spinner },
  props: {
    userId: { type: String, required: true }
  },
  data() {
    return {
      user: null,
      loading: true
    }
  },
  watch: {
    userId: {
      immediate: true,
      handler: 'loadUser'
    }
  },
  methods: {
    async loadUser() {
      this.loading = true;
      this.user = await fetchUser(this.userId);
      this.loading = false;
    }
  }
}
</script>
```

**Vue架构特点**：

- 响应式数据系统实现自动UI更新
- 单文件组件整合模板、逻辑和样式
- 指令系统简化DOM操作
- 渐进式采用支持增量集成
- 依赖跟踪优化重渲染性能

-**Angular架构**

Angular提供了完整的企业级开发平台：

```typescript
// Angular组件示例
@Component({
  selector: 'app-user-profile',
  template: `
    <div *ngIf="user$ | async as user; else loading">
      <h1>{{ user.name }}</h1>
      <app-user-stats [stats]="user.stats"></app-user-stats>
      <app-user-activity [activities]="user.activities"></app-user-activity>
    </div>
    <ng-template #loading>
      <app-spinner></app-spinner>
    </ng-template>
  `
})
export class UserProfileComponent implements OnInit {
  @Input() userId: string;
  user$: Observable<User>;
  
  constructor(private userService: UserService) {}
  
  ngOnInit() {
    this.user$ = this.userService.getUser(this.userId).pipe(
      catchError(error => {
        this.errorService.handle(error);
        return EMPTY;
      })
    );
  }
}
```

**Angular架构特点**：

- 完整的DI(依赖注入)系统促进松耦合
- RxJS与Observable模式处理异步流
- TypeScript原生支持增强类型安全
- 模块化系统支持代码组织
- AOT编译提高运行时性能

-**Svelte与编译时革命**

Svelte代表了向编译时优化转变的前端架构：

```svelte
<!-- Svelte组件示例 -->
<script>
  export let userId;
  
  let user;
  let loading = true;
  
  async function loadUser() {
    loading = true;
    user = await fetchUser(userId);
    loading = false;
  }
  
  $: if (userId) loadUser();
</script>

{#if loading}
  <Spinner />
{:else if user}
  <div class="user-profile">
    <h1>{user.name}</h1>
    <UserStats stats={user.stats} />
    <UserActivity activities={user.activities} />
  </div>
{/if}
```

**Svelte架构特点**：

- 无虚拟DOM，编译为高效命令式DOM更新
- 零运行时依赖，减少包体积
- 反应式声明简化状态管理
- 作用域CSS自动隔离样式
- 编译时静态分析优化性能

-**框架架构比较**

|特性|React|Vue|Angular|Svelte|
|---|---|---|---|---|
|核心范式|函数式组件+Hooks|选项式API/组合式API|类组件+DI|编译时反应式|
|状态管理|单向数据流|响应式系统|Observable+NgRx|编译时反应式|
|DOM渲染|虚拟DOM|虚拟DOM|增量DOM|编译为原生DOM更新|
|学习曲线|中等|低到中|高|低|
|企业适用性|高|高|非常高|中|
|包体积|中|小|大|最小|
|编译优化|部分(JSX)|部分|高(AOT)|最高|

### 2.2 状态管理演进

-**集中式状态管理**

Redux代表了严格单向数据流的状态管理模式：

```javascript
// Redux示例
// 定义Actions
const ADD_TODO = 'ADD_TODO';
const TOGGLE_TODO = 'TOGGLE_TODO';

// Action创建器
const addTodo = text => ({ type: ADD_TODO, text });
const toggleTodo = id => ({ type: TOGGLE_TODO, id });

// Reducer
function todosReducer(state = [], action) {
  switch (action.type) {
    case ADD_TODO:
      return [...state, { id: Date.now(), text: action.text, completed: false }];
    case TOGGLE_TODO:
      return state.map(todo =>
        todo.id === action.id ? { ...todo, completed: !todo.completed } : todo
      );
    default:
      return state;
  }
}

// 中间件处理副作用
const loggingMiddleware = store => next => action => {
  console.log('dispatching', action);
  const result = next(action);
  console.log('next state', store.getState());
  return result;
};
```

**Redux架构特点**：

- 单一数据源(单状态树)
- 状态只读，通过分发Action更改
- Reducer是纯函数，确保可预测性
- 中间件处理副作用和异步操作
- 严格单向数据流增强可维护性

-**响应式状态管理**

MobX代表了响应式状态管理方式：

```javascript
// MobX示例
class TodoStore {
  @observable todos = [];
  
  @computed get completedCount() {
    return this.todos.filter(todo => todo.completed).length;
  }
  
  @action addTodo(text) {
    this.todos.push({ id: Date.now(), text, completed: false });
  }
  
  @action toggleTodo(id) {
    const todo = this.todos.find(todo => todo.id === id);
    if (todo) {
      todo.completed = !todo.completed;
    }
  }
  
  @action.bound async fetchTodos() {
    const response = await api.fetchTodos();
    runInAction(() => {
      this.todos = response.data;
    });
  }
}
```

**MobX架构特点**：

- 响应式追踪自动更新依赖
- 可变状态简化状态修改
- 计算值自动缓存和重计算
- 动作封装状态修改逻辑
- 与OOP范式自然结合

-**原子化状态管理**

Recoil和Jotai代表了原子化状态管理的新趋势：

```javascript
// Recoil示例
// 定义原子状态
const todoListState = atom({
  key: 'todoListState',
  default: []
});

// 派生状态（选择器）
const filteredTodoListState = selector({
  key: 'filteredTodoListState',
  get: ({get}) => {
    const filter = get(todoListFilterState);
    const list = get(todoListState);
    
    switch (filter) {
      case 'completed':
        return list.filter(item => item.completed);
      case 'uncompleted':
        return list.filter(item => !item.completed);
      default:
        return list;
    }
  }
});

// 组件中使用
function TodoList() {
  const [todoList, setTodoList] = useRecoilState(todoListState);
  const filteredTodos = useRecoilValue(filteredTodoListState);
  
  // 使用派生状态渲染UI
}
```

**原子化状态管理特点**：

- 状态分解为最小原子单位
- 派生状态通过选择器计算
- 按需更新减少重渲染
- 与React Suspense自然集成
- 避免了全局状态树的复杂性

-**查询与缓存管理**

React Query和SWR代表了以数据为中心的状态管理新范式：

```javascript
// React Query示例
function TodoApp() {
  // 获取数据，自动处理加载、错误和缓存
  const { data, isLoading, error } = useQuery('todos', fetchTodos, {
    staleTime: 5 * 60 * 1000, // 5分钟内视为新鲜数据
    cacheTime: 60 * 60 * 1000, // 缓存1小时
    retry: 3,  // 失败重试3次
    onSuccess: data => console.log('Data fetched successfully', data)
  });
  
  // 修改数据
  const mutation = useMutation(addTodo, {
    onSuccess: () => {
      // 更新查询缓存
      queryClient.invalidateQueries('todos');
    }
  });
  
  if (isLoading) return <Spinner />;
  if (error) return <ErrorMessage error={error} />;
  
  return (
    <div>
      <TodoList todos={data} />
      <AddTodoForm onSubmit={text => mutation.mutate({ text })} />
    </div>
  );
}
```

**查询状态管理特点**：

- 自动缓存和重新验证
- 乐观更新与回滚
- 请求去重与合并
- 分页和无限滚动支持
- 聚焦重新获取与网络恢复处理

-**状态管理趋势比较**

|特性|Redux|MobX|原子化(Recoil/Jotai)|查询库(React Query)|
|:---:|:----:|:----:|:----:|:----:|
|核心范式|函数式不可变|面向对象可变|原子化组合|数据为中心|
|状态粒度|粗粒度(全局存储)|中粒度(多存储)|细粒度(原子)|资源粒度|
|异步处理|通过中间件|runInAction|选择器+Suspense|内置|
|学习曲线|高|中|低|低|
|调试能力|很强|中等|中等|强|
|适用场景|复杂状态|中等复杂性|组件共享状态|远程数据|

### 2.3 组件设计模式

-**组合模式**

现代组件库越来越倾向于组合设计模式，提供更灵活的使用方式：

```jsx
// 组合组件模式示例
// 传统模式
<Select
  options={[
    { value: 'apple', label: 'Apple' },
    { value: 'banana', label: 'Banana' }
  ]}
  placeholder="Select a fruit"
  onChange={handleChange}
  disabled={isDisabled}
  error={validationError}
/>

// 组合模式
<Select value={value} onChange={setValue}>
  <Select.Trigger aria-label="Select fruit">
    {selectedItem ? selectedItem.label : "Select a fruit"}
  </Select.Trigger>
  <Select.Content>
    <Select.Group>
      <Select.Label>Fruits</Select.Label>
      <Select.Item value="apple">Apple</Select.Item>
      <Select.Item value="banana">Banana</Select.Item>
    </Select.Group>
  </Select.Content>
</Select>
```

**组合模式优势**：

- 更高的灵活性和可定制性
- 符合HTML原生嵌套结构
- 关注点分离更清晰
- 避免属性爆炸问题
- 更好的可访问性控制

-**原子设计系统**

Tailwind CSS和其他原子CSS框架推动了原子设计在前端的应用：

```jsx
// 原子CSS组件示例
function Card({ title, description }) {
  return (
    <div className="rounded-lg shadow-md p-6 bg-white hover:shadow-lg transition-shadow">
      <h2 className="text-xl font-semibold text-gray-800 mb-2">{title}</h2>
      <p className="text-gray-600">{description}</p>
      <button className="mt-4 px-4 py-2 bg-blue-500 text-white rounded hover:bg-blue-600 focus:ring-2 focus:ring-blue-300 focus:outline-none">
        Learn More
      </button>
    </div>
  );
}
```

**原子设计特点**：

- 高度可组合的原子类
- 减少CSS体积和重复
- 在HTML中直接表达设计意图
- 一致的设计约束
- 减少自定义CSS编写

-**状态机组件**

状态机设计模式使组件行为更可预测：

```javascript
// 使用XState的状态机组件
import { useMachine } from '@xstate/react';
import { createMachine } from 'xstate';

const formMachine = createMachine({
  id: 'form',
  initial: 'idle',
  states: {
    idle: {
      on: { SUBMIT: 'submitting' }
    },
    submitting: {
      invoke: {
        src: 'submitForm',
        onDone: 'success',
        onError: 'error'
      }
    },
    success: {
      on: { RESET: 'idle' }
    },
    error: {
      on: { 
        SUBMIT: 'submitting',
        RESET: 'idle'
      }
    }
  }
});

function Form() {
  const [state, send] = useMachine(formMachine, {
    services: {
      submitForm: async (context, event) => {
        return await api.submitForm(formData);
      }
    }
  });
  
  return (
    <form
      onSubmit={(e) => {
        e.preventDefault();
        send('SUBMIT');
      }}
    >
      {/* 根据状态渲染不同UI */}
      {state.matches('error') && <ErrorMessage />}
      {state.matches('success') && <SuccessMessage />}
      
      <button type="submit" disabled={state.matches('submitting')}>
        {state.matches('submitting') ? 'Submitting...' : 'Submit'}
      </button>
    </form>
  );
}
```

**状态机组件特点**：

- 显式定义所有可能状态和转换
- 防止不可能的状态组合
- 简化复杂交互逻辑
- 可视化状态流程
- 提高可测试性

-**服务器组件模式**

React Server Components代表了新的组件架构范式：

```jsx
// React Server Component示例
// UserProfile.server.jsx - 服务器组件
import { db } from '../database';
import { ClientProfileActions } from './ClientProfileActions.client';

export default async function UserProfile({ userId }) {
  // 直接数据库访问，无需API调用
  const user = await db.users.findUnique({ where: { id: userId } });
  const posts = await db.posts.findMany({ where: { authorId: userId } });
  
  return (
    <div>
      <h1>{user.name}</h1>
      <ClientProfileActions userId={user.id} />
      <div>
        {posts.map(post => (
          <PostPreview key={post.id} post={post} />
        ))}
      </div>
    </div>
  );
}

// ClientProfileActions.client.jsx - 客户端组件
'use client';
import { useState } from 'react';

export function ClientProfileActions({ userId }) {
  const [isFollowing, setIsFollowing] = useState(false);
  
  return (
    <button onClick={() => setIsFollowing(!isFollowing)}>
      {isFollowing ? 'Unfollow' : 'Follow'}
    </button>
  );
}
```

**服务器组件特点**：

- 零客户端JavaScript(服务器组件)
- 直接后端资源访问
- 减少客户端bundle大小
- 保持交互组件的客户端渲染
- 无缝流式传输和渐进增强

### 2.4 构建与优化系统

-**现代构建工具**

Vite代表了新一代前端构建工具：

```javascript
// vite.config.js
import { defineConfig } from 'vite';
import react from '@vitejs/plugin-react';
import legacy from '@vitejs/plugin-legacy';
import { visualizer } from 'rollup-plugin-visualizer';

export default defineConfig({
  plugins: [
    react(),
    legacy({
      targets: ['> 1%', 'not IE 11']
    }),
    visualizer()
  ],
  build: {
    target: 'es2015',
    minify: 'terser',
    cssCodeSplit: true,
    rollupOptions: {
      output: {
        manualChunks: {
          vendor: ['react', 'react-dom'],
          ui: ['@mui/material', '@emotion/react']
        }
      }
    }
  },
  server: {
    hmr: true,
    proxy: {
      '/api': {
        target: 'http://localhost:3000',
        changeOrigin: true
      }
    }
  }
});
```

-**Vite架构特点**：

- 基于ESM的开发服务器实现即时启动
- 开发环境无打包，生产环境使用Rollup
- 按需编译提高开发效率
- 优化的HMR提升快速反馈
- 内置支持常见前端工具

-**构建工具比较**

|特性|Webpack|Vite|Parcel|Esbuild|
|---|---|---|---|---|
|开发启动速度|慢|很快|中等|极快|
|配置复杂度|高|中|低|中|
|生态系统|非常丰富|丰富|中等|有限|
|打包策略|全量打包|开发按需/生产打包|自动检测|全量打包|
|代码分割|强大|支持|自动|支持|
|HMR支持|支持|原生ESM支持|支持|有限|
|TypeScript支持|通过loader|原生|内置|原生|

-**性能优化策略**

现代前端项目采用多层次优化策略：

```javascript
// 性能优化配置示例
// webpack.config.js (优化配置)
module.exports = {
  optimization: {
    // 摇树优化
    usedExports: true,
    // 代码分割
    splitChunks: {
      chunks: 'all',
      maxInitialRequests: 25,
      minSize: 20000,
      cacheGroups: {
        defaultVendors: {
          test: /[\\/]node_modules[\\/]/,
          priority: -10,
          reuseExistingChunk: true,
        },
        default: {
          minChunks: 2,
          priority: -20,
          reuseExistingChunk: true,
        },
      },
    },
    // 运行时代码分离
    runtimeChunk: 'single',
  },
  // 资源优化
  module: {
    rules: [
      {
        test: /\.(png|jpg|gif)$/i,
        use: [
          {
            loader: 'image-webpack-loader',
            options: {
              mozjpeg: { progressive: true, quality: 65 },
              optipng: { enabled: true },
              pngquant: { quality: [0.65, 0.90], speed: 4 },
              gifsicle: { interlaced: false },
              webp: { quality: 75 }
            }
          }
        ]
      }
    ]
  }
};

// 代码层面优化
const LazyComponent = React.lazy(() => import('./HeavyComponent'));

function App() {
  return (
    <React.Suspense fallback={<Spinner />}>
      <LazyComponent />
    </React.Suspense>
  );
}
```

**性能优化层次**：

- 构建优化：代码分割、树摇动、压缩
- 加载优化：懒加载、预加载、缓存策略
- 渲染优化：虚拟列表、渲染防抖、批量更新
- 资源优化：图像压缩、字体优化、资源提示
- 运行时优化：Web Workers、渲染队列、计算缓存

## 3. 后端架构

### 3.1 服务器框架比较

-**Node.js生态系统**

Express是最流行的Node.js框架，代表了轻量级的后端设计：

```javascript
// Express应用示例
const express = require('express');
const helmet = require('helmet');
const morgan = require('morgan');
const { body, validationResult } = require('express-validator');

const app = express();

// 中间件配置
app.use(helmet());  // 安全头
app.use(morgan('combined'));  // 日志
app.use(express.json());  // JSON解析

// 路由处理
app.get('/api/users', async (req, res) => {
  try {
    const users = await User.find({}).limit(100);
    res.json(users);
  } catch (error) {
    res.status(500).json({ error: error.message });
  }
});

// 验证中间件
app.post(
  '/api/users',
  [
    body('email').isEmail().normalizeEmail(),
    body('name').trim().isLength({ min: 2, max: 50 })
  ],
  async (req, res) => {
    const errors = validationResult(req);
    if (!errors.isEmpty()) {
      return res.status(400).json({ errors: errors.array() });
    }
    
    try {
      const user = new User(req.body);
      await user.save();
      res.status(201).json(user);
    } catch (error) {
      res.status(500).json({ error: error.message });
    }
  }
);

// 错误处理中间件
app.use((err, req, res, next) => {
  console.error(err.stack);
  res.status(500).json({ error: 'Something broke!' });
});

app.listen(3000, () => {
  console.log('Server running on port 3000');
});
```

**Express架构特点**：

- 中间件架构支持灵活处理请求/响应
- 最小核心支持模块化扩展
- 路由系统组织API端点
- 错误处理中间件集中处理异常
- 活跃生态系统提供各种功能扩展

-**NestJS架构**

NestJS提供了企业级的Node.js框架体验：

```typescript
// NestJS控制器和服务示例
@Controller('users')
```typescript
// NestJS控制器和服务示例
@Controller('users')
export class UsersController {
  constructor(private readonly usersService: UsersService) {}

  @Get()
  @UseGuards(AuthGuard('jwt'))
  findAll(@Query() query: ListUsersDto): Promise<User[]> {
    return this.usersService.findAll(query);
  }

  @Get(':id')
  @UseInterceptors(CacheInterceptor)
  findOne(@Param('id') id: string): Promise<User> {
    return this.usersService.findOne(id);
  }

  @Post()
  @UsePipes(new ValidationPipe())
  create(@Body() createUserDto: CreateUserDto): Promise<User> {
    return this.usersService.create(createUserDto);
  }

  @Delete(':id')
  @Roles('admin')
  remove(@Param('id') id: string): Promise<void> {
    return this.usersService.remove(id);
  }
}

@Injectable()
export class UsersService {
  constructor(
    @InjectRepository(User)
    private usersRepository: Repository<User>,
    private eventEmitter: EventEmitter2
  ) {}

  async findAll(query: ListUsersDto): Promise<User[]> {
    return this.usersRepository.find({
      take: query.limit,
      skip: query.offset,
      where: query.filter
    });
  }

  async findOne(id: string): Promise<User> {
    const user = await this.usersRepository.findOne(id);
    if (!user) {
      throw new NotFoundException(`User with ID ${id} not found`);
    }
    return user;
  }

  async create(data: CreateUserDto): Promise<User> {
    const user = this.usersRepository.create(data);
    await this.usersRepository.save(user);
    this.eventEmitter.emit('user.created', user);
    return user;
  }

  async remove(id: string): Promise<void> {
    const result = await this.usersRepository.delete(id);
    if (result.affected === 0) {
      throw new NotFoundException(`User with ID ${id} not found`);
    }
  }
}
```

**NestJS架构特点**：

- 依赖注入系统促进松耦合
- 模块化架构支持大型应用组织
- 装饰器风格API提高代码可读性
- 拦截器、守卫和管道提供横切关注点
- TypeScript优先设计增强类型安全

-**Go语言web框架**

Go的Echo框架代表了高性能后端框架：

```go
// Echo框架示例
package main

import (
  "net/http"
  
  "github.com/labstack/echo/v4"
  "github.com/labstack/echo/v4/middleware"
  "gorm.io/gorm"
)

type User struct {
  ID    uint   `json:"id" gorm:"primaryKey"`
  Name  string `json:"name" validate:"required,min=2"`
  Email string `json:"email" validate:"required,email"`
}

type UserHandler struct {
  DB *gorm.DB
}

func (h *UserHandler) GetUsers(c echo.Context) error {
  var users []User
  result := h.DB.Find(&users)
  if result.Error != nil {
    return echo.NewHTTPError(http.StatusInternalServerError, result.Error.Error())
  }
  return c.JSON(http.StatusOK, users)
}

func (h *UserHandler) CreateUser(c echo.Context) error {
  u := new(User)
  if err := c.Bind(u); err != nil {
    return echo.NewHTTPError(http.StatusBadRequest, err.Error())
  }
  
  if err := c.Validate(u); err != nil {
    return echo.NewHTTPError(http.StatusBadRequest, err.Error())
  }
  
  result := h.DB.Create(u)
  if result.Error != nil {
    return echo.NewHTTPError(http.StatusInternalServerError, result.Error.Error())
  }
  
  return c.JSON(http.StatusCreated, u)
}

func main() {
  e := echo.New()
  e.Validator = &CustomValidator{validator: validator.New()}
  
  // 中间件
  e.Use(middleware.Logger())
  e.Use(middleware.Recover())
  e.Use(middleware.CORS())
  
  // 数据库连接
  db, _ := gorm.Open(sqlite.Open("test.db"), &gorm.Config{})
  db.AutoMigrate(&User{})
  
  // 处理器
  h := &UserHandler{DB: db}
  
  // 路由
  e.GET("/users", h.GetUsers)
  e.POST("/users", h.CreateUser)
  
  e.Logger.Fatal(e.Start(":8080"))
}
```

**Go架构特点**：

- 高并发处理能力
- 中间件链实现横切关注点
- 路由系统支持REST API设计
- 简洁的错误处理模式
- 强类型系统增强安全性

-**框架比较**

|特性|Express (Node.js)|NestJS (Node.js)|Echo (Go)|Spring Boot (Java)|Django (Python)|
|---|---|---|---|---|---|
|架构风格|中间件|模块化/依赖注入|中间件|依赖注入|MTV|
|性能|中|中|高|高|中|
|内存使用|低|中|低|高|中|
|企业适用性|中|高|高|最高|高|
|学习曲线|低|中高|中|高|中|
|类型系统|可选|原生TypeScript|静态|静态|动态|
|异步模型|回调/Promise/Async|Promise/Async|Goroutine|多线程|同步/异步|

### 3.2 API设计范式

-**REST API设计**

REST仍然是最常见的API设计模式：

```javascript
// RESTful API示例 - Express
const router = express.Router();

// 资源集合
router.get('/articles', articleController.listArticles);
router.post('/articles', authenticate, validateArticle, articleController.createArticle);

// 单一资源
router.get('/articles/:id', articleController.getArticle);
router.put('/articles/:id', authenticate, validateArticle, articleController.updateArticle);
router.patch('/articles/:id', authenticate, validatePartialArticle, articleController.partialUpdateArticle);
router.delete('/articles/:id', authenticate, authorize, articleController.deleteArticle);

// 嵌套资源
router.get('/articles/:articleId/comments', commentController.listComments);
router.post('/articles/:articleId/comments', authenticate, validateComment, commentController.createComment);

// 查询参数示例
// GET /articles?category=tech&sort=recent&page=2&limit=10
```

**REST设计特点**：

- 资源导向的URL结构
- HTTP方法定义操作类型
- 状态码表示操作结果
- 分页和过滤通过查询参数
- 版本控制(通常通过URL或头部)

-**GraphQL API设计**

GraphQL提供了更灵活的数据查询方式：

```javascript
// GraphQL Schema定义
const typeDefs = gql`
  type User {
    id: ID!
    name: String!
    email: String!
    posts: [Post!]!
    following: [User!]!
  }
  
  type Post {
    id: ID!
    title: String!
    content: String!
    published: Boolean!
    author: User!
    comments: [Comment!]!
    categories: [Category!]!
    createdAt: DateTime!
  }
  
  type Comment {
    id: ID!
    text: String!
    author: User!
    post: Post!
    createdAt: DateTime!
  }
  
  type Query {
    users(first: Int, skip: Int): [User!]!
    user(id: ID!): User
    posts(first: Int, skip: Int, where: PostWhereInput): [Post!]!
    post(id: ID!): Post
  }
  
  type Mutation {
    createUser(data: CreateUserInput!): User!
    updateUser(id: ID!, data: UpdateUserInput!): User
    deleteUser(id: ID!): User
    createPost(data: CreatePostInput!): Post!
    publishPost(id: ID!): Post
  }
  
  input CreateUserInput {
    name: String!
    email: String!
    password: String!
  }
  
  input UpdateUserInput {
    name: String
    email: String
  }
  
  input PostWhereInput {
    published: Boolean
    title_contains: String
    author: UserWhereInput
  }
`;

// 解析器实现
const resolvers = {
  Query: {
    users: (_, args, { prisma }) => {
      return prisma.user.findMany({
        take: args.first,
        skip: args.skip
      });
    },
    user: (_, { id }, { prisma }) => {
      return prisma.user.findUnique({
        where: { id }
      });
    },
    // 其他查询解析器
  },
  Mutation: {
    createUser: async (_, { data }, { prisma }) => {
      const hashedPassword = await bcrypt.hash(data.password, 10);
      return prisma.user.create({
        data: {
          ...data,
          password: hashedPassword
        }
      });
    },
    // 其他变更解析器
  },
  User: {
    posts: (parent, _, { prisma }) => {
      return prisma.post.findMany({
        where: { authorId: parent.id }
      });
    },
    // 其他字段解析器
  }
};
```

**GraphQL特点**：

- 客户端指定需要的确切数据
- 单个请求获取多资源数据
- 强类型Schema自文档化
- 解析器架构灵活处理数据源
- 订阅支持实时更新

-**gRPC设计**

gRPC代表了高性能RPC通信方式：

```protobuf
// gRPC协议定义 - user.proto
syntax = "proto3";

package user;

service UserService {
  // 创建用户
  rpc CreateUser(CreateUserRequest) returns (User) {}
  
  // 获取用户信息
  rpc GetUser(GetUserRequest) returns (User) {}
  
  // 更新用户
  rpc UpdateUser(UpdateUserRequest) returns (User) {}
  
  // 删除用户
  rpc DeleteUser(DeleteUserRequest) returns (DeleteUserResponse) {}
  
  // 获取用户列表
  rpc ListUsers(ListUsersRequest) returns (ListUsersResponse) {}
  
  // 流式获取用户活动
  rpc StreamUserActivity(UserActivityRequest) returns (stream UserActivity) {}
}

message User {
  string id = 1;
  string name = 2;
  string email = 3;
  UserStatus status = 4;
  int64 created_at = 5;
}

enum UserStatus {
  ACTIVE = 0;
  INACTIVE = 1;
  BANNED = 2;
}

message CreateUserRequest {
  string name = 1;
  string email = 2;
  string password = 3;
}

message GetUserRequest {
  string id = 1;
}

message UpdateUserRequest {
  string id = 1;
  optional string name = 2;
  optional string email = 3;
  optional UserStatus status = 4;
}

message DeleteUserRequest {
  string id = 1;
}

message DeleteUserResponse {
  bool success = 1;
}

message ListUsersRequest {
  int32 page_size = 1;
  string page_token = 2;
  UserStatus status = 3;
}

message ListUsersResponse {
  repeated User users = 1;
  string next_page_token = 2;
  int32 total_size = 3;
}

message UserActivityRequest {
  string user_id = 1;
  int64 since_timestamp = 2;
}

message UserActivity {
  string id = 1;
  string user_id = 2;
  ActivityType activity_type = 3;
  string resource_id = 4;
  int64 timestamp = 5;
}

enum ActivityType {
  LOGIN = 0;
  LOGOUT = 1;
  CREATE = 2;
  UPDATE = 3;
  DELETE = 4;
}
```

**gRPC特点**：

- 基于HTTP/2的高性能通信
- 紧凑的二进制协议格式
- 强类型接口定义语言(IDL)
- 代码生成简化客户端/服务器实现
- 支持流式请求和响应

-**API架构比较**

|特性|REST|GraphQL|gRPC|
|---|---|---|---|
|协议|HTTP|HTTP|HTTP/2|
|数据格式|JSON/XML|JSON|Protocol Buffers|
|类型系统|无/OpenAPI|强类型Schema|强类型IDL|
|灵活查询|有限|高度灵活|有限|
|缓存|原生HTTP缓存|需自定义|需自定义|
|客户端简便性|高|中|需代码生成|
|传输效率|中|中|高|
|双向流|无|有限(订阅)|完全支持|
|适用场景|通用Web API|灵活数据需求|微服务/内部服务|

### 3.3 微服务与单体架构

-**单体应用架构**

传统单体应用架构示例：

```java
// Spring Boot单体应用示例 - 分层架构
@SpringBootApplication
public class EcommerceApplication {
    public static void main(String[] args) {
        SpringApplication.run(EcommerceApplication.class, args);
    }
}

// 控制器层
@RestController
@RequestMapping("/api/products")
public class ProductController {
    private final ProductService productService;
    
    @Autowired
    public ProductController(ProductService productService) {
        this.productService = productService;
    }
    
    @GetMapping
    public Page<ProductDTO> getAllProducts(
            @RequestParam(defaultValue = "0") int page,
            @RequestParam(defaultValue = "10") int size) {
        return productService.findAllProducts(PageRequest.of(page, size));
    }
    
    // 其他API端点
}

// 服务层
@Service
@Transactional
public class ProductServiceImpl implements ProductService {
    private final ProductRepository productRepository;
    private final CategoryRepository categoryRepository;
    private final ProductMapper productMapper;
    
    @Autowired
    public ProductServiceImpl(
            ProductRepository productRepository,
            CategoryRepository categoryRepository,
            ProductMapper productMapper) {
        this.productRepository = productRepository;
        this.categoryRepository = categoryRepository;
        this.productMapper = productMapper;
    }
    
    @Override
    public Page<ProductDTO> findAllProducts(Pageable pageable) {
        Page<Product> productsPage = productRepository.findAll(pageable);
        return productsPage.map(productMapper::toDto);
    }
    
    // 其他业务逻辑
}

// 数据访问层
@Repository
public interface ProductRepository extends JpaRepository<Product, Long> {
    List<Product> findByCategoryId(Long categoryId);
    
    @Query("SELECT p FROM Product p WHERE p.price BETWEEN :min AND :max")
    List<Product> findByPriceRange(@Param("min") BigDecimal min, @Param("max") BigDecimal max);
}

// 实体层
@Entity
@Table(name = "products")
public class Product {
    @Id
    @GeneratedValue(strategy = GenerationType.IDENTITY)
    private Long id;
    
    @Column(nullable = false)
    private String name;
    
    private String description;
    
    @Column(nullable = false)
    private BigDecimal price;
    
    @ManyToOne(fetch = FetchType.LAZY)
    @JoinColumn(name = "category_id")
    private Category category;
    
    // 其他字段、getter和setter
}
```

**单体架构特点**：

- 单一部署单元简化运维
- 共享内存和数据库简化开发
- 分层架构分离关注点
- 紧密耦合增加开发团队协调成本
- 整体扩展而非按需扩展

-**微服务架构**

典型微服务架构示例：

```java
// 产品服务 - 分布式微服务示例
@SpringBootApplication
@EnableDiscoveryClient
public class ProductServiceApplication {
    public static void main(String[] args) {
        SpringApplication.run(ProductServiceApplication.class, args);
    }
}

@RestController
@RequestMapping("/products")
public class ProductController {
    private final ProductService productService;
    
    // API实现
}

// 服务间通信 - Feign Client示例
@FeignClient(name = "inventory-service")
public interface InventoryClient {
    @GetMapping("/inventory/{productId}")
    InventoryResponse checkInventory(@PathVariable("productId") Long productId);
}

// 使用断路器模式处理服务间通信
@Service
public class ProductServiceImpl implements ProductService {
    private final ProductRepository productRepository;
    private final InventoryClient inventoryClient;
    
    @CircuitBreaker(name = "inventoryService", fallbackMethod = "getDefaultInventory")
    public ProductDetailDTO getProductWithInventory(Long id) {
        Product product = productRepository.findById(id)
            .orElseThrow(() -> new ResourceNotFoundException("Product not found"));
            
        // 调用库存服务获取库存信息
        InventoryResponse inventory = inventoryClient.checkInventory(id);
        
        ProductDetailDTO dto = mapper.toDetailDto(product);
        dto.setAvailableQuantity(inventory.getQuantity());
        dto.setInStock(inventory.isInStock());
        
        return dto;
    }
    
    // 断路器回退方法
    public ProductDetailDTO getDefaultInventory(Long id, Exception ex) {
        Product product = productRepository.findById(id)
            .orElseThrow(() -> new ResourceNotFoundException("Product not found"));
            
        ProductDetailDTO dto = mapper.toDetailDto(product);
        dto.setAvailableQuantity(0);
        dto.setInStock(false);
        
        // 记录失败
        log.error("Inventory service is down. Using fallback for product: {}", id, ex);
        
        return dto;
    }
}
```

-**微服务配置 - 服务注册与发现**

```yaml
# application.yml
spring:
  application:
    name: product-service
  cloud:
    consul:
      host: consul
      port: 8500
      discovery:
        instanceId: ${spring.application.name}:${random.uuid}
        healthCheckPath: /actuator/health
        healthCheckInterval: 15s

# 配置中心集成
  config:
    import: optional:configserver:http://config-server:8888

# 分布式追踪
  zipkin:
    base-url: http://zipkin:9411
    
# 消息队列配置
  kafka:
    bootstrap-servers: kafka:9092
    producer:
      key-serializer: org.apache.kafka.common.serialization.StringSerializer
      value-serializer: org.springframework.kafka.support.serializer.JsonSerializer
```

**微服务架构特点**：

- 服务按业务能力组织
- 独立部署和扩展
- 技术栈多样性
- 服务间通过网络通信
- 弹性设计处理部分失败
- 复杂的分布式系统挑战

-**微服务与单体比较**

|特性|单体架构|微服务架构|
|---|---|---|
|部署复杂性|低|高|
|开发复杂性|低(小规模) / 高(大规模)|中|
|技术栈灵活性|低|高|
|扩展性|粗粒度|细粒度|
|故障隔离|差|好|
|团队协作|紧密耦合|自治团队|
|测试复杂性|低|高|
|监控复杂性|低|高|
|适用场景|小团队 / 初创|大型组织 / 复杂领域|

### 3.4 函数即服务(FaaS)

-**AWS Lambda架构**

以AWS Lambda为例的无服务器架构：

```javascript
// AWS Lambda函数示例 - Node.js
const AWS = require('aws-sdk');
const dynamodb = new AWS.DynamoDB.DocumentClient();

exports.handler = async (event) => {
  try {
    // API Gateway事件处理
    const { pathParameters, httpMethod, body } = event;
    const id = pathParameters?.id;
    
    // 路由逻辑
    if (httpMethod === 'GET') {
      if (id) {
        return await getItem(id);
      } else {
        return await listItems();
      }
    } else if (httpMethod === 'POST') {
      const item = JSON.parse(body);
      return await createItem(item);
    } else if (httpMethod === 'PUT' && id) {
      const item = JSON.parse(body);
      return await updateItem(id, item);
    } else if (httpMethod === 'DELETE' && id) {
      return await deleteItem(id);
    }
    
    // 未支持的操作
    return {
      statusCode: 400,
      body: JSON.stringify({ error: 'Unsupported operation' })
    };
  } catch (error) {
    return {
      statusCode: 500,
      body: JSON.stringify({ error: error.message })
    };
  }
};

// 数据库操作
async function getItem(id) {
  const params = {
    TableName: process.env.TABLE_NAME,
    Key: { id }
  };
  
  const result = await dynamodb.get(params).promise();
  
  if (!result.Item) {
    return {
      statusCode: 404,
      body: JSON.stringify({ error: 'Item not found' })
    };
  }
  
  return {
    statusCode: 200,
    body: JSON.stringify(result.Item)
  };
}

// 其他CRUD操作...
```

-**AWS Lambda的基础设施配置 - 使用AWS CDK**

```typescript
// AWS CDK基础设施配置
import * as cdk from 'aws-cdk-lib';
import { Construct } from 'constructs';
import * as lambda from 'aws-cdk-lib/aws-lambda';
import * as apigateway from 'aws-cdk-lib/aws-apigateway';
import * as dynamodb from 'aws-cdk-lib/aws-dynamodb';
import * as iam from 'aws-cdk-lib/aws-iam';

export class ItemsServiceStack extends cdk.Stack {
  constructor(scope: Construct, id: string, props?: cdk.StackProps) {
    super(scope, id, props);
    
    // DynamoDB表
    const itemsTable = new dynamodb.Table(this, 'ItemsTable', {
      partitionKey: { name: 'id', type: dynamodb.AttributeType.STRING },
      billingMode: dynamodb.BillingMode.PAY_PER_REQUEST,
      removalPolicy: cdk.RemovalPolicy.DESTROY, // 开发环境
    });
    
    // Lambda函数
    const itemsFunction = new lambda.Function(this, 'ItemsFunction', {
      runtime: lambda.Runtime.NODEJS_14_X,
      handler: 'index.handler',
      code: lambda.Code.fromAsset('lambda'),
      environment: {
        TABLE_NAME: itemsTable.tableName
      }
    });
    
    // 授予Lambda访问DynamoDB的权限
    itemsTable.grantReadWriteData(itemsFunction);
    
    // API Gateway
    const api = new apigateway.RestApi(this, 'ItemsApi', {
      restApiName: 'Items Service',
      description: 'API for managing items'
    });
    
    // 资源和方法
    const items = api.root.addResource('items');
    const singleItem = items.addResource('{id}');
    
    const itemsIntegration = new apigateway.LambdaIntegration(itemsFunction);
    
    // CRUD操作
    items.addMethod('GET', itemsIntegration);  // 列出所有
    items.addMethod('POST', itemsIntegration);  // 创建
    singleItem.addMethod('GET', itemsIntegration);  // 获取单个
    singleItem.addMethod('PUT', itemsIntegration);  // 更新
    singleItem.addMethod('DELETE', itemsIntegration);  // 删除
  }
}
```

**FaaS架构特点**：

- 事件驱动设计
- 扩展至零（不使用时不产生费用）
- 按使用量计费
- 无状态函数设计
- 冷启动延迟权衡
- 与云服务深度集成

-**无服务器框架 - Serverless Framework**

```yaml
# serverless.yml
service: items-service

provider:
  name: aws
  runtime: nodejs14.x
  region: us-east-1
  environment:
    TABLE_NAME: ${self:service}-${self:provider.stage}
  iamRoleStatements:
    - Effect: Allow
      Action:
        - dynamodb:Query
        - dynamodb:Scan
        - dynamodb:GetItem
        - dynamodb:PutItem
        - dynamodb:UpdateItem
        - dynamodb:DeleteItem
      Resource: !GetAtt ItemsTable.Arn

functions:
  api:
    handler: index.handler
    events:
      - http:
          path: /items
          method: GET
      - http:
          path: /items
          method: POST
      - http:
          path: /items/{id}
          method: GET
      - http:
          path: /items/{id}
          method: PUT
      - http:
          path: /items/{id}
          method: DELETE

resources:
  Resources:
    ItemsTable:
      Type: AWS::DynamoDB::Table
      Properties:
        TableName: ${self:service}-${self:provider.stage}
        BillingMode: PAY_PER_REQUEST
        AttributeDefinitions:
          - AttributeName: id
            AttributeType: S
        KeySchema:
          - AttributeName: id
            KeyType: HASH
```

-**FaaS与传统架构比较**

|特性|FaaS (无服务器)|传统服务器|容器化微服务|
|---|---|---|---|
|基础设施管理|最小|完全自管理|部分管理(容器编排)|
|扩展模型|自动/精细|手动/粗粒度|自动/容器级别|
|定价模型|按使用量|固定+可变|资源使用|
|启动时间|毫秒~秒(冷启动)|已运行|秒级|
|最大运行时间|有限(分钟级)|无限|无限|
|状态管理|外部服务|内存/本地|容器内或外部|
|开发复杂性|低|中|高|
|运维复杂性|低|高|中高|

## 4. 数据存储与处理

### 4.1 关系型数据库现状

-**PostgreSQL高级特性**

PostgreSQL代表了现代关系型数据库的强大功能：

```sql
-- PostgreSQL高级功能示例

-- JSON数据类型和操作
CREATE TABLE orders (
  id SERIAL PRIMARY KEY,
  customer_id INTEGER NOT NULL,
  order_date TIMESTAMP WITH TIME ZONE DEFAULT NOW(),
  status VARCHAR(50) NOT NULL,
  items JSONB NOT NULL,
  metadata JSONB
);

-- JSON查询和索引
CREATE INDEX idx_items ON orders USING GIN (items);

-- 复杂JSON查询
SELECT id, customer_id, items
FROM orders
WHERE items @> '[{"product_id": 123, "quantity": 2}]'::jsonb
  AND (metadata->>'priority')::int > 3;

-- 表继承
CREATE TABLE products (
  id SERIAL PRIMARY KEY,
  name VARCHAR(255) NOT NULL,
  price DECIMAL(10, 2) NOT NULL,
  created_at TIMESTAMP WITH TIME ZONE DEFAULT NOW()
);

CREATE TABLE digital_products (
  download_url VARCHAR(255) NOT NULL,
  file_size_bytes BIGINT
) INHERITS (products);

CREATE TABLE physical_products (
  weight_kg DECIMAL(8, 3),
  dimensions VARCHAR(100),
  inventory_count INTEGER
) INHERITS (products);

-- 查询所有产品
SELECT * FROM products;
-- 只查询特定类型
SELECT * FROM ONLY digital_products;

-- 高级数据类型
CREATE TABLE user_locations (
  user_id INTEGER PRIMARY KEY,
  location POINT,  -- 空间数据类型
  search_radius CIRCLE,
  home_address VARCHAR(255),
  ip_range INET,  -- 网络地址类型
  available_times TSRANGE[]  -- 时间范围数组
);

-- 查找某个位置附近的用户
SELECT user_id, location
FROM user_locations
WHERE circle(point(40.7128, -74.0060), 5000) @> location;

-- 全文搜索
CREATE TABLE articles (
  id SERIAL PRIMARY KEY,
  title VARCHAR(255) NOT NULL,
  content TEXT NOT NULL,
  published_at TIMESTAMP WITH TIME ZONE,
  search_vector TSVECTOR
);

-- 全文搜索索引
CREATE INDEX articles_search_idx ON articles USING GIN (search_vector);

-- 更新触发器生成搜索向量
CREATE FUNCTION articles_search_trigger() RETURNS trigger AS $$
BEGIN
  NEW.search_vector := 
    setweight(to_tsvector('english', NEW.title), 'A') ||
    setweight(to_tsvector('english', NEW.content), 'B');
  RETURN NEW;
END
$$ LANGUAGE plpgsql;

CREATE TRIGGER articles_search_update
BEFORE INSERT OR UPDATE ON articles
FOR EACH ROW EXECUTE PROCEDURE articles_search_trigger();

-- 全文搜索查询
SELECT id, title
FROM articles
WHERE search_vector @@ to_tsquery('english', 'machine & learning')
ORDER BY ts_rank(search_vector, to_tsquery('english', 'machine & learning')) DESC;
```

**PostgreSQL架构特点**：

- 高级数据类型支持（JSON, 几何类型, 范围类型）
- 表继承和分区支持
- 强大的索引选项（B-tree, GIN, GIST）
- 全文搜索能力
- 可扩展性与插件系统
- 强事务和ACID保证

-**MySQL与MariaDB**

MySQL/MariaDB的现代特性和优化：

```sql
-- MySQL/MariaDB高级功能示例

-- InnoDB表配置
CREATE TABLE orders (
  id BIGINT UNSIGNED AUTO_INCREMENT PRIMARY KEY,
  customer_id INT UNSIGNED NOT NULL,
  order_date DATETIME NOT NULL DEFAULT CURRENT_TIMESTAMP,
  total DECIMAL(10, 2) NOT NULL,
  status ENUM('pending', 'processing', 'shipped', 'delivered', 'cancelled') NOT NULL,
  INDEX idx_customer (customer_id),
  INDEX idx_date (order_date),
  INDEX idx_status (status)
) ENGINE=InnoDB ROW_FORMAT=DYNAMIC;

-- JSON支持
CREATE TABLE product_details (
  product_id INT UNSIGNED PRIMARY KEY,
  details JSON NOT NULL,
  INDEX idx_details ((CAST(details->>'$.category' AS CHAR(64))))
);

-- 插入JSON数据
INSERT INTO product_details VALUES (
  101, 
  '{
    "name": "Ergonomic Chair",
    "category": "furniture",
    "specs": {
      "weight_kg": 12.5,
      "dimensions": {
        "width_cm": 60,
        "height_cm": 120,
        "depth_cm": 65
      },
      "materials": ["metal", "fabric", "plastic"]
    },
    "colors_available": ["black", "grey", "blue"]
  }'
);

-- JSON查询
SELECT product_id, 
       details->>'$.name' AS name,
       details->>'$.category' AS category,
       details->>'$.specs.weight_kg' AS weight
FROM product_details
WHERE details->>'$.category' = 'furniture'
  AND JSON_CONTAINS(details->>'$.colors_available', '"black"');

-- 窗口函数
SELECT 
  o.id, 
  o.customer_id,
  o.total,
  o.order_date,
  SUM(o.total) OVER (PARTITION BY o.customer_id) AS customer_lifetime_value,
  SUM(o.total) OVER (PARTITION BY o.customer_id ORDER BY o.order_date) AS running_total,
  DENSE_RANK() OVER (PARTITION BY o.customer_id ORDER BY o.total DESC) AS order_rank_by_value
FROM orders o
WHERE o.order_date >= DATE_SUB(CURRENT_DATE(), INTERVAL 1 YEAR);

-- 通用表表达式(CTE)
WITH repeat_customers AS (
  SELECT customer_id, COUNT(*) AS order_count
  FROM orders
  WHERE order_date >= DATE_SUB(CURRENT_DATE(), INTERVAL 1 YEAR)
  GROUP BY customer_id
  HAVING COUNT(*) > 1
),
high_value_customers AS (
  SELECT customer_id, SUM(total) AS total_spent
  FROM orders
  WHERE order_date >= DATE_SUB(CURRENT_DATE(), INTERVAL 1 YEAR)
  GROUP BY customer_id
  HAVING SUM(total) > 1000
)
SELECT c.id, c.name, c.email, r.order_count, h.total_spent
FROM customers c
JOIN repeat_customers r ON c.id = r.customer_id
JOIN high_value_customers h ON c.id = h.customer_id
ORDER BY h.total_spent DESC;
```

**MySQL/MariaDB架构特点**：

- 多存储引擎架构（InnoDB, MyISAM等）
- 主从复制和Group Replication
- 分区表支持
- JSON数据类型和函数
- 全文索引
- 窗口函数和CTE支持

-**NewSQL数据库**

CockroachDB代表了分布式SQL数据库的新范式：

```sql
-- CockroachDB分布式SQL示例

-- 创建表并设置主键
CREATE TABLE users (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  email VARCHAR(255) NOT NULL UNIQUE,
  name VARCHAR(100),
  created_at TIMESTAMPTZ NOT NULL DEFAULT now(),
  updated_at TIMESTAMPTZ
);

-- 定义表分区和复制
ALTER TABLE users CONFIGURE ZONE USING
  num_replicas = 5,
  constraints = '{"+region=us-west1": 1, "+region=us-east1": 1, "+region=eu-west1": 1}',
  lease_preferences = '[[+region=us-west1], [+region=us-east1], [+region=eu-west1]]';

-- 创建地理分布的多区域索引
CREATE INDEX idx_users_email ON users (email) STORING (name);
ALTER INDEX idx_users_email CONFIGURE ZONE USING
  num_replicas = 3,
  constraints = '{"+region=us-east1": 1, "+region=eu-west1": 1}',
  lease_preferences = '[[+region=eu-west1]]';

-- 分布式事务
BEGIN;
  INSERT INTO orders (id, user_id, total) VALUES (gen_random_uuid(), 'a0eebc99-9c0b-4ef8-bb6d-6bb9bd380a11', 199.99);
  UPDATE users SET last_order_date = now() WHERE id = 'a0eebc99-9c0b-4ef8-bb6d-6bb9bd380a11';
COMMIT;

-- 序列化隔离保证
-- 即使在分布式环境中也能保持ACID特性
BEGIN TRANSACTION ISOLATION LEVEL SERIALIZABLE;
  -- 用户余额检查和更新
  SELECT balance FROM accounts WHERE id = 'account1' FOR UPDATE;
  -- 确保余额足够
  UPDATE accounts SET balance = balance - 100 WHERE id = 'account1';
  UPDATE accounts SET balance = balance + 100 WHERE id = 'account2';
COMMIT;

-- 存活时间(TTL)
CREATE TABLE sessions (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  user_id UUID NOT NULL REFERENCES users(id),
  data JSONB,
  created_at TIMESTAMPTZ NOT NULL DEFAULT now(),
  expires_at TIMESTAMPTZ NOT NULL DEFAULT (now() + INTERVAL '24 hours')
);

-- 创建TTL任务
CREATE TABLE session_cleanup (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  ts TIMESTAMPTZ NOT NULL DEFAULT now(),
  cleanup_after TIMESTAMPTZ NOT NULL
);

-- 使用作业调度清理过期会话
CREATE SCHEDULE cleanup_expired_sessions
  FOR DELETE FROM sessions WHERE expires_at < now()
  WITH SCHEDULE '0 */1 * * *';
```

**NewSQL特点**：

- 水平可扩展性保持SQL语义
- 自动分片和复制
- 强一致性和分布式事务
- 高可用和容错设计
- 地理分布支持
- 兼容现有SQL工具和ORM

-**关系型数据库比较**

|特性|PostgreSQL|MySQL/MariaDB|CockroachDB|
|---|---|---|---|
|架构|单节点/有限集群|主从/组复制|分布式/多活|
|扩展方式|垂直/读写分离|垂直/水平(分库分表)|自动水平分片|
|一致性|强|可配置|强(线性一致性)|
|数据类型|非常丰富|丰富|丰富|
|索引类型|多样(B-tree/GIN/GIST)|有限(B-tree/哈希)|多样但有限制|
|SQL兼容性|高度标准兼容|中(方言)|PostgreSQL兼容|
|JSON支持|原生(JSONB)|中等|支持|
|地理数据|PostGIS|有限|原生支持|
|云原生|需适配|需适配|原生设计|

### 4.2 NoSQL解决方案

-**文档数据库 - MongoDB**

MongoDB代表了灵活的文档存储模型：

```javascript
// MongoDB架构设计示例

// 集合设计 - 电子商务应用
// 产品集合
db.products.insertOne({
  name: "Ultra HD Smart TV",
  slug: "ultra-hd-smart-tv",
  sku: "TV-UHD-55",
  price: 699.99,
  salePrice: 599.99,
  category: "electronics",
  tags: ["tv", "smart-tv", "ultra-hd", "55-inch"],
  attributes: {
    brand: "TechView",
    modelNumber: "TV-55UHD-2021",
    displaySize: 55,
    resolution: "3840x2160",
    refreshRate: 120,
    hdrSupport: true,
    smartFeatures: ["Netflix", "YouTube", "Amazon Prime"]
  },
  inventory: {
    inStock: true,
    quantity: 45,
    warehouse: "EAST-5"
  },
  images: [
    {
      url: "https://example.com/products/tv-55-main.jpg",
      alt: "Front view of 55 inch TV",
      isPrimary: true
    },
    {
      url: "https://example.com/products/tv-55-angle.jpg",
      alt: "Angle view of 55 inch TV",
      isPrimary: false
    }
  ],
  ratings: {
    average: 4.7,
    count: 142
  },
  createdAt: new Date(),
  updatedAt: new Date()
});

// 索引创建
db.products.createIndex({ name: "text", description: "text" });
db.products.createIndex({ slug: 1 }, { unique: true });
db.products.createIndex({ category: 1, "attributes.brand": 1 });
db.products.createIndex({ "inventory.quantity": 1 });

// 聚合管道查询
db.orders.aggregate([
  // 匹配最近30天的订单
  {
    $match: {
      orderDate: { $gte: new Date(Date.now() - 30 * 24 * 60 * 60 * 1000) },
      status: "completed"
    }
  },
  // 展开订单项
  {
    $unwind: "$items"
  },
  // 分组计算每个产品的销售额
  {
    $group: {
      _id: "$items.productId",
      totalQuantity: { $sum: "$items.quantity" },
      totalRevenue: { $sum: { $multiply: ["$items.price", "$items.quantity"] } },
      orderCount: { $sum: 1 }
    }
  },
  // 连接产品集合获取产品信息
  {
    $lookup: {
      from: "products",
      localField: "_id",
      foreignField: "_id",
      as: "product"
    }
  },
  // 展平产品数组
  {
    $unwind: "$product"
  },
  // 重塑输出格式
  {
    $project: {
      _id: 0,
      productId: "$_id",
      productName: "$product.name",
      category: "$product.category",
      brand: "$product.attributes.brand",
      totalQuantity: 1,
      totalRevenue: 1,
      orderCount: 1,
      averageOrderValue: { $divide: ["$totalRevenue", "$orderCount"] }
    }
  },
  // 按收入排序
  {
    $sort: { totalRevenue: -1 }
  },
  // 限制结果
  {
    $limit: 20
  }
]);

// 事务示例
const session = db.getMongo().startSession();
session.startTransaction();

try {
  // 更新库存
  const inventoryResult = db.products.updateOne(
    {
      _id: productId,
      "inventory.quantity": { $gte: quantity }
    },
    {
      $inc: { "inventory.quantity": -quantity }
    },
    { session }
  );
  
  if (inventoryResult.modifiedCount !== 1) {
    throw new Error("Insufficient inventory");
  }
  
  // 创建订单
  const orderResult = db.orders.insertOne({
    userId: userId,
    items: [{ productId, quantity, price }],
    total: quantity * price,
    status: "pending",
    createdAt: new Date()
  }, { session });
  
  // 更新用户订单历史
  db.users.updateOne(
    { _id: userId },
    {
      $push: { orderIds: orderResult.insertedId },
      $inc: { orderCount: 1 }
    },
    { session }
  );
  
  // 提交事务
  session.commitTransaction();
} catch (error) {
  // 回滚事务
  session.abortTransaction();
  throw error;
} finally {
  session.endSession();
}
```

**MongoDB架构特点**：

- 灵活的文档模型无需预定义Schema
- 自动分片支持水平扩展
- 复制集提供高可用性
- 原生支持地理空间索引
- 强大的聚合框架
- 支持ACID事务

-**键值存储 - Redis**

Redis作为高性能键值存储和多功能数据结构服务器：

```bash
# Redis数据结构和命令示例

# 字符串操作 - 计数器和缓存
SET pageviews:homepage 1000
INCR pageviews:homepage
GET pageviews:homepage

# 带过期时间的缓存
SET user:profile:1001 "{\"name\":\"John\",\"email\":\"john@example.com\"}" EX 3600
GET user:profile:1001

# 哈希表 - 存储对象
HSET product:10001 name "Smartphone X" price 699.99 category "electronics" stock 124
HINCRBY product:10001 stock -1
HGETALL product:10001

# 列表 - 最新动态、消息队列
LPUSH latest:news "{\"id\":1,\"title\":\"New Feature Launch\"}"
LPUSH latest:news "{\"id\":2,\"title\":\"System Maintenance\"}"
LRANGE latest:news 0 4

# 任务队列
RPUSH tasks:email "{\"type\":\"welcome\",\"user_id\":1001}"
LPOP tasks:email

# 集合 - 唯一元素集合、标签系统
SADD product:10001:tags "smartphone" "5g" "android"
SADD product:10002:tags "smartphone" "5g" "ios"
SINTER product:10001:tags product:10002:tags  # 共同标签

# 用户在线状态
SADD online:users 1001 1002 1003
SISMEMBER online:users 1001  # 检查用户是否在线

# 有序集合 - 排行榜、权重列表
ZADD leaderboard:monthly 1220 "user:1001"
ZADD leaderboard:monthly 940 "user:1002" 
ZADD leaderboard:monthly 1500 "user:1003"
ZREVRANGE leaderboard:monthly 0 9 WITHSCORES  # 前10名

# 位图操作 - 用户活跃统计
SETBIT user:1001:active:2023-08 0 1  # 8月1日活跃
SETBIT user:1001:active:2023-08 5 1  # 8月6日活跃
BITCOUNT user:1001:active:2023-08  # 活跃天数

# 地理空间 - 位置服务
GEOADD locations 13.361389 38.115556 "store:1001" 15.087269 37.502669 "store:1002"
GEODIST locations "store:1001" "store:1002" km
GEORADIUS locations 15.0 37.0 50 km

# 流 - 事件处理、日志
XADD events:purchases * product_id 10001 user_id 1001 quantity 2
XADD events:purchases * product_id 10002 user_id 1002 quantity 1
XREAD COUNT 10 STREAMS events:purchases 0-0

# 发布订阅
SUBSCRIBE notifications:global
PUBLISH notifications:global "{\"type\":\"alert\",\"message\":\"System update\"}"

# Lua脚本 - 原子操作
EVAL "
local current = tonumber(redis.call('get', KEYS[1])) or 0
if current >= tonumber(ARGV[1]) then
  redis.call('decrby', KEYS[1], ARGV[1])
  return 1
else
  return 0
end
" 1 inventory:10001 5
```

**Redis架构特点**：

- 内存数据存储带持久化选项
- 多种数据结构支持复杂场景
- 单线程主执行模型简化并发
- 支持主从复制和哨兵模式
- 集群模式实现水平扩展
- 发布订阅和流处理支持
- Lua脚本支持原子操作

-**列存储 - Cassandra**

Apache Cassandra为大规模分布式存储设计：

```cql
-- Cassandra数据模型和CQL示例

-- 创建键空间(数据库)并设置复制策略
CREATE KEYSPACE ecommerce
WITH REPLICATION = {
  'class': 'NetworkTopologyStrategy',
  'datacenter1': 3,
  'datacenter2': 2
};

USE ecommerce;

-- 以查询为驱动的表设计 - 用户订单
CREATE TABLE user_orders (
  user_id UUID,
  order_id TIMEUUID,
  order_date TIMESTAMP,
  order_status TEXT,
  total DECIMAL,
  shipping_address TEXT,
  payment_method TEXT,
  PRIMARY KEY (user_id, order_id)
) WITH CLUSTERING ORDER BY (order_id DESC);

-- 创建二级索引
CREATE INDEX ON user_orders (order_status);

-- 产品信息表
CREATE TABLE products (
  product_id UUID,
  name TEXT,
  description TEXT,
  price DECIMAL,
  category TEXT,
  tags SET<TEXT>,
  attributes MAP<TEXT, TEXT>,
  created_at TIMESTAMP,
  PRIMARY KEY (product_id)
);

-- 按类别查询的产品表 - 查询模式复制
CREATE TABLE products_by_category (
  category TEXT,
  product_id UUID,
  name TEXT,
  price DECIMAL,
  created_at TIMESTAMP,
  PRIMARY KEY (category, product_id)
) WITH CLUSTERING ORDER BY (product_id ASC);

-- 每个购物车有多个物品 - 复合主键和聚类列
CREATE TABLE shopping_cart_items (
  cart_id UUID,
  product_id UUID,
  added_at TIMESTAMP,
  quantity INT,
  price DECIMAL,
  product_name TEXT,
  PRIMARY KEY (cart_id, product_id)
);

-- 时间序列数据 - 产品库存历史
CREATE TABLE product_inventory_history (
  product_id UUID,
  timestamp TIMESTAMP,
  quantity INT,
  warehouse TEXT,
  operation TEXT,
  PRIMARY KEY (product_id, timestamp)
) WITH CLUSTERING ORDER BY (timestamp DESC);

-- 插入数据
INSERT INTO user_orders (
  user_id, order_id, order_date, order_status, total, 
  shipping_address, payment_method
) VALUES (
  123e4567-e89b-12d3-a456-426614174000,
  now(),
  toTimestamp(now()),
  'processing',
  129.99,
  '123 Main St, City, Country',
  'credit_card'
);

-- 轻量级事务 (CAS - Compare And Set)
UPDATE products 
SET price = 599.99 
WHERE product_id = 123e4567-e89b-12d3-a456-426614174000
IF price = 649.99;

-- 批处理操作
BEGIN BATCH
  INSERT INTO products (product_id, name, price, category)
  VALUES (123e4567-e89b-12d3-a456-426614174000, 'Smart Watch', 299.99, 'electronics');
  
  INSERT INTO products_by_category (category, product_id, name, price, created_at)
  VALUES ('electronics', 123e4567-e89b-12d3-a456-426614174000, 'Smart Watch', 299.99, toTimestamp(now()));
APPLY BATCH;

-- 使用TTL自动过期数据
INSERT INTO session_tokens (user_id, token, created_at)
VALUES (123e4567-e89b-12d3-a456-426614174000, 'auth-token-xyz', toTimestamp(now()))
USING TTL 86400;  -- 24小时后过期
```

**Cassandra架构特点**：

- 分布式、去中心化设计
- 线性可扩展性
- 多数据中心复制
- 无单点故障设计
- 面向列的存储模型
- Gossip协议的节点发现
- 一致性级别可配置

-**时序数据库 - InfluxDB**

InfluxDB为时间序列数据优化：

```sql
-- InfluxDB示例查询

-- 创建连续查询进行自动降采样
CREATE CONTINUOUS QUERY "cq_30m_system_metrics" ON "monitoring"
BEGIN
  SELECT 
    mean("cpu_usage") AS "cpu_usage",
    mean("memory_usage") AS "memory_usage",
    mean("disk_usage") AS "disk_usage",
    mean("network_in") AS "network_in",
    mean("network_out") AS "network_out"
  INTO "monitoring"."autogen"."system_metrics_30m"
  FROM "system_metrics"
  GROUP BY time(30m), "host", "service"
END

-- 使用Flux查询语言进行复杂分析
from(bucket: "monitoring")
  |> range(start: -1d)
  |> filter(fn: (r) => r._measurement == "system_metrics")
  |> filter(fn: (r) => r.host =~ /app-server-.*/)
  |> filter(fn: (r) => r._field == "cpu_usage" or r._field == "memory_usage")
  |> aggregateWindow(every: 5m, fn: mean)
  |> pivot(rowKey: ["_time"], columnKey: ["_field"], valueColumn: "_value")
  |> map(fn: (r) => ({
      _time: r._time,
      host: r.host,
      cpu: r.cpu_usage,
      memory: r.memory_usage,
      cpu_memory_ratio: r.cpu_usage / r.memory_usage
    })
  )
  |> filter(fn: (r) => r.cpu > 80.0 or r.memory > 90.0)
  |> yield(name: "high_utilization")

-- 使用InfluxQL查询API请求延迟的99百分位数
SELECT percentile("response_time", 99) 
FROM "api_metrics" 
WHERE time >= now() - 30m 
  AND "service" = 'user-service'
  AND "endpoint" = '/api/users'
GROUP BY time(1m), "host"

-- 查找异常值 - 偏离均值超过2个标准差的点
SELECT "response_time" 
FROM "api_metrics" 
WHERE "service" = 'payment-service'
  AND time >= now() - 6h
  AND ("response_time" > (
    SELECT mean("response_time") + (2 * stddev("response_time"))
    FROM "api_metrics"
    WHERE "service" = 'payment-service'
      AND time >= now() - 6h
  ) OR "response_time" < (
    SELECT mean("response_time") - (2 * stddev("response_time"))
    FROM "api_metrics"
    WHERE "service" = 'payment-service'
      AND time >= now() - 6h
  ))

-- 创建保留策略管理数据生命周期
CREATE RETENTION POLICY "short_term" ON "monitoring" DURATION 7d REPLICATION 3 DEFAULT
CREATE RETENTION POLICY "long_term" ON "monitoring" DURATION 365d REPLICATION 2

-- 使用Kapacitor定义警报
// Kapacitor TICK脚本示例
stream
    |from()
        .measurement('cpu')
    |alert()
        .crit(lambda: "usage_idle" < 10)
        .message('{{ .Level }} alert: {{ .Name }} Host: {{ index .Tags "host" }} has high CPU usage: {{ index .Fields "usage_idle" }}')
        .slack()
```

**InfluxDB架构特点**：

- 针对时间序列数据优化
- 高写入吞吐量
- 自动数据老化和降采样
- 强大的函数库支持时序分析
- 内置保留策略管理数据生命周期
- 与Telegraf、Kapacitor集成

-**NoSQL数据库比较**

|特性|MongoDB|Redis|Cassandra|InfluxDB|
|---|---|---|---|---|
|数据模型|文档|键值/数据结构|宽列|时间序列|
|查询语言|MongoDB查询/聚合|命令集|CQL (类SQL)|InfluxQL/Flux|
|扩展模型|分片+复制集|主从/集群|去中心化环|集群|
|一致性|可配置|强一致|可调一致性|可配置|
|事务支持|ACID事务|仅脚本原子|轻量级事务|有限|
|持久化|日志+快照|RDB/AOF|日志+SSTable|TSM|
|主要用途|通用/应用数据|缓存/实时数据|大规模分布式|指标/监控|
|特殊功能|地理空间|数据结构|高写入容量|时序分析|

### 4.3 数据访问层模式

-**ORM模式**

TypeORM示例展示现代ORM的功能：

```typescript
// TypeORM实体和关系示例

// 实体定义
@Entity()
export class User {
  @PrimaryGeneratedColumn('uuid')
  id: string;

  @Column({ length: 100 })
  name: string;

  @Column({ unique: true })
  email: string;

  @Column({ select: false })  // 默认查询不返回密码
  password: string;

  @CreateDateColumn()
  createdAt: Date;

  @UpdateDateColumn()
  updatedAt: Date;
  
  @OneToMany(() => Order, order => order.user)
  orders: Order[];
  
  @ManyToMany(() => Role)
  @JoinTable()
  roles: Role[];
}

@Entity()
export class Order {
  @PrimaryGeneratedColumn('uuid')
  id: string;

  @ManyToOne(() => User, user => user.orders)
  user: User;

  @Column({ type: 'decimal', precision: 10, scale: 2 })
  total: number;

  @Column({
    type: 'enum',
    enum: OrderStatus,
    default: OrderStatus.PENDING
  })
  status: OrderStatus;

  @OneToMany(() => OrderItem, item => item.order, { cascade: true })
  items: OrderItem[];

  @CreateDateColumn()
  createdAt: Date;

  @UpdateDateColumn()
  updatedAt: Date;
}

// 复合索引和高级特性
@Entity()
@Index(['name', 'category'])
export class Product {
  @PrimaryGeneratedColumn('uuid')
  id: string;

  @Column()
  name: string;

  @Column()
  category: string;

  @Column({ type: 'decimal', precision: 10, scale: 2 })
  price: number;

  @Column({ type: 'jsonb', nullable: true })
  attributes: Record<string, any>;

  @Column({ default: true })
  isActive: boolean;

  @Column({ type: 'int', default: 0 })
  stock: number;

  @OneToMany(() => OrderItem, item => item.product)
  orderItems: OrderItem[];
}

// 实际使用ORM的服务类
@Injectable()
export class ProductService {
  constructor(
    @InjectRepository(Product)
    private productRepository: Repository<Product>
  ) {}

  async findAll(options: {
    category?: string;
    minPrice?: number;
    maxPrice?: number;
    inStock?: boolean;
    page?: number;
    limit?: number;
    sort?: string;
  }): Promise<{ items: Product[]; total: number }> {
    const { category, minPrice, maxPrice, inStock, page = 1, limit = 
10, sort = 'name:asc' } = options;
    
    // 构建查询构建器
    const queryBuilder = this.productRepository.createQueryBuilder('product');
    
    // 应用过滤条件
    if (category) {
      queryBuilder.andWhere('product.category = :category', { category });
    }
    
    if (minPrice !== undefined) {
      queryBuilder.andWhere('product.price >= :minPrice', { minPrice });
    }
    
    if (maxPrice !== undefined) {
      queryBuilder.andWhere('product.price <= :maxPrice', { maxPrice });
    }
    
    if (inStock !== undefined) {
      queryBuilder.andWhere(inStock ? 'product.stock > 0' : 'product.stock = 0');
    }
    
    // 默认只返回活跃产品
    queryBuilder.andWhere('product.isActive = true');
    
    // 应用排序
    const [sortField, sortDirection] = sort.split(':');
    queryBuilder.orderBy(`product.${sortField}`, sortDirection.toUpperCase() as 'ASC' | 'DESC');
    
    // 应用分页
    const skip = (page - 1) * limit;
    queryBuilder.skip(skip).take(limit);
    
    // 执行查询
    const [items, total] = await queryBuilder.getManyAndCount();
    
    return { items, total };
  }
  
  async findOne(id: string): Promise<Product> {
    const product = await this.productRepository.findOne({
      where: { id },
      relations: ['orderItems', 'orderItems.order']
    });
    
    if (!product) {
      throw new NotFoundException(`Product with ID ${id} not found`);
    }
    
    return product;
  }
  
  async create(data: Partial<Product>): Promise<Product> {
    const product = this.productRepository.create(data);
    return await this.productRepository.save(product);
  }
  
  async update(id: string, data: Partial<Product>): Promise<Product> {
    await this.productRepository.update(id, data);
    return this.findOne(id);
  }
  
  async remove(id: string): Promise<void> {
    const result = await this.productRepository.delete(id);
    
    if (result.affected === 0) {
      throw new NotFoundException(`Product with ID ${id} not found`);
    }
  }
  
  // 事务示例
  async createProductWithInventory(
    productData: Partial<Product>,
    initialStock: number
  ): Promise<Product> {
    return this.productRepository.manager.transaction(async manager => {
      // 创建产品
      const productRepo = manager.getRepository(Product);
      const product = productRepo.create({
        ...productData,
        stock: 0 // 初始库存为0
      });
      
      await productRepo.save(product);
      
      // 创建库存记录
      const inventoryRepo = manager.getRepository(Inventory);
      const inventory = inventoryRepo.create({
        product,
        quantity: initialStock,
        warehouseId: 'main'
      });
      
      await inventoryRepo.save(inventory);
      
      // 更新产品库存
      product.stock = initialStock;
      await productRepo.save(product);
      
      return product;
    });
  }
}
```

**ORM架构特点**：

- 实体映射提供面向对象接口
- 关系处理自动连接相关数据
- 迁移系统管理数据库结构演变
- 数据库无关性支持多种后端
- 懒加载和预加载优化性能
- 查询构建器提供灵活的查询能力

-**数据映射器模式**

SQLAlchemy核心API展示数据映射器模式：

```python
# SQLAlchemy数据映射器示例

from sqlalchemy import (
    create_engine, MetaData, Table, Column, Integer, String, 
    Numeric, DateTime, ForeignKey, select, func, and_, or_
)
from sqlalchemy.ext.declarative import declarative_base
from datetime import datetime

# 创建数据库连接
engine = create_engine('postgresql://user:password@localhost:5432/mydb')
metadata = MetaData()

# 使用核心API定义表
users = Table(
    'users', metadata,
    Column('id', Integer, primary_key=True),
    Column('name', String(100), nullable=False),
    Column('email', String(255), unique=True, nullable=False),
    Column('created_at', DateTime, default=datetime.utcnow)
)

orders = Table(
    'orders', metadata,
    Column('id', Integer, primary_key=True),
    Column('user_id', Integer, ForeignKey('users.id')),
    Column('total', Numeric(10, 2), nullable=False),
    Column('status', String(50), nullable=False),
    Column('created_at', DateTime, default=datetime.utcnow)
)

order_items = Table(
    'order_items', metadata,
    Column('id', Integer, primary_key=True),
    Column('order_id', Integer, ForeignKey('orders.id')),
    Column('product_id', Integer, ForeignKey('products.id')),
    Column('quantity', Integer, nullable=False),
    Column('price', Numeric(10, 2), nullable=False)
)

products = Table(
    'products', metadata,
    Column('id', Integer, primary_key=True),
    Column('name', String(100), nullable=False),
    Column('description', String, nullable=True),
    Column('price', Numeric(10, 2), nullable=False),
    Column('stock', Integer, default=0),
    Column('category', String(50), nullable=True),
    Column('created_at', DateTime, default=datetime.utcnow)
)

# 创建表
metadata.create_all(engine)

# 数据访问类
class UserRepository:
    def __init__(self, connection):
        self.connection = connection
    
    def find_by_id(self, user_id):
        query = select([users]).where(users.c.id == user_id)
        result = self.connection.execute(query).fetchone()
        return dict(result) if result else None
    
    def find_by_email(self, email):
        query = select([users]).where(users.c.email == email)
        result = self.connection.execute(query).fetchone()
        return dict(result) if result else None
    
    def create(self, user_data):
        result = self.connection.execute(users.insert().values(**user_data))
        user_id = result.inserted_primary_key[0]
        return self.find_by_id(user_id)
    
    def update(self, user_id, user_data):
        self.connection.execute(
            users.update()
            .where(users.c.id == user_id)
            .values(**user_data)
        )
        return self.find_by_id(user_id)
    
    def delete(self, user_id):
        self.connection.execute(
            users.delete().where(users.c.id == user_id)
        )

class OrderRepository:
    def __init__(self, connection):
        self.connection = connection
    
    def find_with_items(self, order_id):
        # 多表连接查询
        query = select([
            orders,
            users.c.name.label('user_name'),
            users.c.email.label('user_email')
        ]).select_from(
            orders.join(users, orders.c.user_id == users.c.id)
        ).where(orders.c.id == order_id)
        
        order_result = self.connection.execute(query).fetchone()
        
        if not order_result:
            return None
        
        order_dict = dict(order_result)
        
        # 查询订单项
        items_query = select([
            order_items,
            products.c.name.label('product_name'),
            products.c.category.label('product_category')
        ]).select_from(
            order_items.join(products, order_items.c.product_id == products.c.id)
        ).where(order_items.c.order_id == order_id)
        
        items_result = self.connection.execute(items_query).fetchall()
        order_dict['items'] = [dict(item) for item in items_result]
        
        return order_dict
    
    def create_with_items(self, order_data, items_data):
        # 使用事务
        with self.connection.begin():
            # 创建订单
            order_result = self.connection.execute(
                orders.insert().values(**order_data)
            )
            order_id = order_result.inserted_primary_key[0]
            
            # 创建订单项
            for item in items_data:
                item['order_id'] = order_id
                self.connection.execute(
                    order_items.insert().values(**item)
                )
                
                # 更新产品库存
                self.connection.execute(
                    products.update()
                    .where(products.c.id == item['product_id'])
                    .values(stock=products.c.stock - item['quantity'])
                )
            
            # 返回完整订单
            return self.find_with_items(order_id)

# 使用示例
with engine.connect() as conn:
    user_repo = UserRepository(conn)
    order_repo = OrderRepository(conn)
    
    # 创建用户
    user = user_repo.create({
        'name': 'John Doe',
        'email': 'john@example.com'
    })
    
    # 创建订单
    order = order_repo.create_with_items(
        {
            'user_id': user['id'],
            'total': 59.98,
            'status': 'pending'
        },
        [
            {
                'product_id': 1,
                'quantity': 2,
                'price': 29.99
            }
        ]
    )
```

**数据映射器特点**：

- 分离数据模型和数据访问逻辑
- 显式SQL和表映射提供精细控制
- 灵活性高于ORM但冗长
- 性能优化机会更多
- 与关系型数据库的特性紧密集成

-**存储库模式**

Spring Data展示存储库模式的优雅实现：

```java
// Spring Data JPA存储库模式示例

// 实体定义
@Entity
@Table(name = "products")
public class Product {
    @Id
    @GeneratedValue(strategy = GenerationType.IDENTITY)
    private Long id;
    
    @Column(nullable = false)
    private String name;
    
    @Column(length = 2000)
    private String description;
    
    @Column(nullable = false)
    private BigDecimal price;
    
    @Column(name = "inventory_count")
    private Integer inventoryCount;
    
    @ManyToOne(fetch = FetchType.EAGER)
    @JoinColumn(name = "category_id")
    private Category category;
    
    @OneToMany(mappedBy = "product", cascade = CascadeType.ALL, orphanRemoval = true)
    private List<ProductReview> reviews = new ArrayList<>();
    
    // getters, setters, etc.
}

// 存储库接口 - 声明式查询
public interface ProductRepository extends JpaRepository<Product, Long> {
    // 基于方法名的查询定义
    List<Product> findByCategoryId(Long categoryId);
    
    List<Product> findByPriceBetween(BigDecimal min, BigDecimal max);
    
    @Query("SELECT p FROM Product p WHERE p.inventoryCount > 0 AND p.category.name = :category")
    List<Product> findInStockByCategory(@Param("category") String category);
    
    // 原生SQL查询
    @Query(value = 
        "SELECT p.*, AVG(r.rating) as avg_rating " +
        "FROM products p " +
        "LEFT JOIN product_reviews r ON p.id = r.product_id " +
        "GROUP BY p.id " +
        "HAVING AVG(r.rating) >= :minRating", 
        nativeQuery = true)
    List<Product> findWithMinimumAverageRating(@Param("minRating") double minRating);
    
    // 分页和排序
    Page<Product> findByNameContaining(String name, Pageable pageable);
    
    // 修改查询
    @Modifying
    @Transactional
    @Query("UPDATE Product p SET p.inventoryCount = p.inventoryCount - :quantity WHERE p.id = :id AND p.inventoryCount >= :quantity")
    int reduceInventory(@Param("id") Long id, @Param("quantity") int quantity);
}

// 自定义存储库实现
public interface CustomProductRepository {
    List<Product> findComplexQuery(ProductSearchCriteria criteria);
}

public class CustomProductRepositoryImpl implements CustomProductRepository {
    @PersistenceContext
    private EntityManager entityManager;
    
    @Override
    public List<Product> findComplexQuery(ProductSearchCriteria criteria) {
        CriteriaBuilder cb = entityManager.getCriteriaBuilder();
        CriteriaQuery<Product> query = cb.createQuery(Product.class);
        Root<Product> root = query.from(Product.class);
        
        // 构建复杂查询条件
        List<Predicate> predicates = new ArrayList<>();
        
        if (criteria.getCategories() != null && !criteria.getCategories().isEmpty()) {
            predicates.add(root.get("category").in(criteria.getCategories()));
        }
        
        if (criteria.getMinPrice() != null) {
            predicates.add(cb.greaterThanOrEqualTo(root.get("price"), criteria.getMinPrice()));
        }
        
        if (criteria.getMaxPrice() != null) {
            predicates.add(cb.lessThanOrEqualTo(root.get("price"), criteria.getMaxPrice()));
        }
        
        if (criteria.getSearchTerm() != null) {
            predicates.add(cb.or(
                cb.like(cb.lower(root.get("name")), "%" + criteria.getSearchTerm().toLowerCase() + "%"),
                cb.like(cb.lower(root.get("description")), "%" + criteria.getSearchTerm().toLowerCase() + "%")
            ));
        }
        
        query.where(predicates.toArray(new Predicate[0]));
        
        // 应用排序
        if (criteria.getSortBy() != null) {
            if (criteria.getSortDirection() == SortDirection.ASC) {
                query.orderBy(cb.asc(root.get(criteria.getSortBy())));
            } else {
                query.orderBy(cb.desc(root.get(criteria.getSortBy())));
            }
        }
        
        return entityManager.createQuery(query)
                .setFirstResult(criteria.getOffset())
                .setMaxResults(criteria.getLimit())
                .getResultList();
    }
}

// 服务层
@Service
@Transactional(readOnly = true)
public class ProductService {
    private final ProductRepository productRepository;
    
    @Autowired
    public ProductService(ProductRepository productRepository) {
        this.productRepository = productRepository;
    }
    
    public List<Product> findByCategory(Long categoryId) {
        return productRepository.findByCategoryId(categoryId);
    }
    
    public Page<Product> searchProducts(String keyword, int page, int size) {
        Pageable pageable = PageRequest.of(page, size, Sort.by("name").ascending());
        return productRepository.findByNameContaining(keyword, pageable);
    }
    
    @Transactional
    public boolean purchaseProduct(Long productId, int quantity) {
        int updated = productRepository.reduceInventory(productId, quantity);
        return updated > 0;
    }
    
    @Transactional
    public Product saveProduct(Product product) {
        return productRepository.save(product);
    }
}
```

**存储库模式特点**：

- 提供领域对象的集合接口
- 隐藏数据访问细节
- 声明式查询定义
- 与领域驱动设计自然契合
- 集成测试能力强
- 组合查询方法支持复杂场景

-**数据访问模式比较**

|特性|ORM|数据映射器|存储库|
|---|---|---|---|
|抽象级别|高|中|高|
|代码量|少|多|中|
|性能控制|有限|强|中|
|查询灵活性|中|高|中高|
|数据库无关性|强|中|强|
|学习曲线|陡峭|中等|平缓|
|适用场景|中小应用|高性能需求|领域驱动设计|

### 4.4 缓存策略与实现

-**多级缓存架构**

现代应用通常采用多级缓存策略：

```java
// Spring Cache多级缓存实现示例

@Configuration
@EnableCaching
public class CacheConfig {
    
    @Bean
    public CacheManager cacheManager(RedisConnectionFactory redisConnectionFactory) {
        // 设置序列化器
        RedisSerializer<String> redisSerializer = new StringRedisSerializer();
        Jackson2JsonRedisSerializer<Object> jackson2JsonRedisSerializer = new Jackson2JsonRedisSerializer<>(Object.class);
        
        // 本地缓存配置
        Map<String, RedisCacheConfiguration> cacheConfigurations = new HashMap<>();
        
        // 产品缓存 - 短TTL, 高频访问
        cacheConfigurations.put("products", RedisCacheConfiguration.defaultCacheConfig()
                .entryTtl(Duration.ofMinutes(10))
                .serializeKeysWith(RedisSerializationContext.SerializationPair.fromSerializer(redisSerializer))
                .serializeValuesWith(RedisSerializationContext.SerializationPair.fromSerializer(jackson2JsonRedisSerializer)));
        
        // 类别缓存 - 长TTL, 不常变化
        cacheConfigurations.put("categories", RedisCacheConfiguration.defaultCacheConfig()
                .entryTtl(Duration.ofHours(24))
                .serializeKeysWith(RedisSerializationContext.SerializationPair.fromSerializer(redisSerializer))
                .serializeValuesWith(RedisSerializationContext.SerializationPair.fromSerializer(jackson2JsonRedisSerializer)));
        
        // 用户会话缓存 - 中等TTL
        cacheConfigurations.put("userSessions", RedisCacheConfiguration.defaultCacheConfig()
                .entryTtl(Duration.ofHours(2))
                .serializeKeysWith(RedisSerializationContext.SerializationPair.fromSerializer(redisSerializer))
                .serializeValuesWith(RedisSerializationContext.SerializationPair.fromSerializer(jackson2JsonRedisSerializer)));
        
        // 创建复合缓存管理器
        CompositeCacheManager compositeCacheManager = new CompositeCacheManager();
        
        // 第一级: Caffeine本地缓存
        CaffeineCacheManager caffeineCacheManager = new CaffeineCacheManager();
        caffeineCacheManager.setCacheNames(Arrays.asList("products", "categories"));
        caffeineCacheManager.setCaffeine(Caffeine.newBuilder()
                .maximumSize(10_000)
                .expireAfterWrite(5, TimeUnit.MINUTES)
                .recordStats());
        
        // 第二级: Redis分布式缓存
        RedisCacheManager redisCacheManager = RedisCacheManager.builder(redisConnectionFactory)
                .cacheDefaults(RedisCacheConfiguration.defaultCacheConfig().entryTtl(Duration.ofMinutes(30)))
                .withInitialCacheConfigurations(cacheConfigurations)
                .build();
        
        // 组合缓存管理器
        compositeCacheManager.setCacheManagers(Arrays.asList(
                caffeineCacheManager, 
                redisCacheManager
        ));
        
        // 设置降级策略
        compositeCacheManager.setFallbackToNoOpCache(true);
        
        return compositeCacheManager;
    }
    
    // 缓存统计和监控
    @Bean
    public CacheMetricsRegistrar cacheMetricsRegistrar(CacheManager cacheManager, MeterRegistry registry) {
        return new CacheMetricsRegistrar(cacheManager, registry);
    }
}

// 在服务中使用缓存
@Service
public class ProductService {
    private final ProductRepository productRepository;
    private final CacheManager cacheManager;
    
    // 声明式缓存
    @Cacheable(value = "products", key = "#id", unless = "#result == null")
    public Product findById(Long id) {
        return productRepository.findById(id).orElse(null);
    }
    
    @Cacheable(value = "products", key = "'category_' + #categoryId")
    public List<Product> findByCategory(Long categoryId) {
        return productRepository.findByCategoryId(categoryId);
    }
    
    @CachePut(value = "products", key = "#result.id")
    public Product save(Product product) {
        return productRepository.save(product);
    }
    
    @CacheEvict(value = "products", key = "#id")
    public void delete(Long id) {
        productRepository.deleteById(id);
    }
    
    // 更复杂的缓存场景 - 批量更新
    @Caching(evict = {
        @CacheEvict(value = "products", key = "#product.id"),
        @CacheEvict(value = "products", key = "'category_' + #product.category.id"),
        @CacheEvict(value = "categories", allEntries = true)
    })
    public Product updateProductWithCategory(Product product) {
        return productRepository.save(product);
    }
    
    // 编程式缓存访问
    public List<Product> findFeaturedProducts() {
        Cache cache = cacheManager.getCache("products");
        ValueWrapper cached = cache.get("featured_products");
        
        if (cached != null) {
            return (List<Product>) cached.get();
        }
        
        List<Product> featuredProducts = productRepository.findFeaturedProducts();
        cache.put("featured_products", featuredProducts);
        
        return featuredProducts;
    }
    
    // 自定义缓存逻辑 - 缓存预热
    @PostConstruct
    public void warmupCache() {
        List<Category> allCategories = categoryRepository.findAll();
        allCategories.forEach(category -> {
            List<Product> products = productRepository.findByCategoryId(category.getId());
            // 预先加载热门类别产品到缓存
            cacheManager.getCache("products").put("category_" + category.getId(), products);
        });
    }
    
    // 缓存降级模式
    public List<Product> searchWithCacheFallback(String query) {
        try {
            // 尝试从缓存获取
            return searchFromCache(query);
        } catch (RedisConnectionException e) {
            // Redis连接失败，降级到数据库直接查询
            log.warn("Redis cache unavailable, falling back to database", e);
            return productRepository.search(query);
        }
    }
}
```

**多级缓存架构特点**：

- 本地缓存(内存)提供最快访问
- 分布式缓存支持跨服务实例共享
- TTL和过期策略管理数据生命周期
- 缓存命中率监控和优化
- 缓存失效和一致性处理
- 降级和回退机制保证可用性

-**缓存模式与策略**

常见缓存模式实现：

```javascript
// Node.js中的各种缓存模式示例

// 导入依赖
const Redis = require('ioredis');
const NodeCache = require('node-cache');
const { promisify } = require('util');
const crypto = require('crypto');

// 缓存客户端
const redisClient = new Redis({
  host: 'redis-server',
  port: 6379,
  retryStrategy: times => Math.min(times * 50, 2000)
});

// 本地内存缓存
const localCache = new NodeCache({
  stdTTL: 300,  // 5分钟默认过期
  checkperiod: 60  // 每分钟检查过期
});

// 1. Cache-Aside模式
class CacheAsideService {
  async getUser(userId) {
    // 先查本地缓存
    const localKey = `user:${userId}`;
    const localData = localCache.get(localKey);
    if (localData) {
      console.log('Local cache hit');
      return localData;
    }
    
    // 再查Redis
    const redisKey = `user:${userId}`;
    let userData = await redisClient.get(redisKey);
    
    if (userData) {
      console.log('Redis cache hit');
      userData = JSON.parse(userData);
      // 回填本地缓存
      localCache.set(localKey, userData);
      return userData;
    }
    
    // 缓存未命中，查数据库
    console.log('Cache miss, querying database');
    const user = await getUserFromDatabase(userId);
    
    if (user) {
      // 写入缓存
      redisClient.set(redisKey, JSON.stringify(user), 'EX', 3600); // 1小时过期
      localCache.set(localKey, user);
    }
    
    return user;
  }
  
  async updateUser(userId, userData) {
    // 先更新数据库
    await updateUserInDatabase(userId, userData);
    
    // 再使缓存失效
    const redisKey = `user:${userId}`;
    await redisClient.del(redisKey);
    localCache.del(`user:${userId}`);
  }
}

// 2. Read-Through缓存
class ReadThroughCache {
  constructor(dataLoader) {
    this.dataLoader = dataLoader; // 数据加载函数
    this.redis = redisClient;
  }
  
  async get(key, options = { ttl: 3600 }) {
    // 尝试从缓存获取
    let data = await this.redis.get(key);
    
    // 缓存未命中
    if (!data) {
      console.log(`Cache miss for key: ${key}`);
      // 加载新数据
      data = await this.dataLoader(key);
      
      // 数据存在则缓存
      if (data) {
        await this.redis.set(key, JSON.stringify(data), 'EX', options.ttl);
      }
      
      return data;
    }
    
    // 缓存命中
    console.log(`Cache hit for key: ${key}`);
    return JSON.parse(data);
  }
}

// 3. Write-Through缓存
class WriteThroughCache {
  constructor(dataWriter) {
    this.dataWriter = dataWriter; // 数据写入函数
    this.redis = redisClient;
  }
  
  async set(key, data, options = { ttl: 3600 }) {
    // 先写入数据库
    await this.dataWriter(key, data);
    
    // 再更新缓存
    await this.redis.set(key, JSON.stringify(data), 'EX', options.ttl);
    
    return data;
  }
}

// 4. Write-Behind缓存 (写回)
class WriteBehindCache {
  constructor(batchWriter, options = { maxBatchSize: 100, flushIntervalMs: 5000 }) {
    this.batchWriter = batchWriter;
    this.options = options;
    this.redis = redisClient;
    this.writeQueue = [];
    this.flushTimer = null;
    
    // 启动定时刷新
    this.startFlushTimer();
  }
  
  startFlushTimer() {
    this.flushTimer = setInterval(() => this.flush(), this.options.flushIntervalMs);
  }
  
  async set(key, data) {
    // 先更新缓存
    await this.redis.set(key, JSON.stringify(data));
    
    // 将写操作加入队列
    this.writeQueue.push({ key, data, timestamp: Date.now() });
    
    // 如果队列超过阈值，立即刷新
    if (this.writeQueue.length >= this.options.maxBatchSize) {
      this.flush();
    }
    
    return data;
  }
  
  async flush() {
    if (this.writeQueue.length === 0) return;
    
    const batch = this.writeQueue.splice(0, this.options.maxBatchSize);
    try {
      await this.batchWriter(batch);
      console.log(`Flushed ${batch.length} items to database`);
    } catch (error) {
      console.error('Error flushing cache to database:', error);
      // 失败时，将项目放回队列
      this.writeQueue.unshift(...batch);
    }
  }
  
  async shutdown() {
    clearInterval(this.flushTimer);
    return this.flush(); // 最终刷新
  }
}

// 5. 缓存穿透保护
class CachingService {
  // 空结果缓存 - 防止缓存穿透
  async getUserWithProtection(userId) {
    const cacheKey = `user:${userId}`;
    
    // 查询缓存
    let cachedData = await redisClient.get(cacheKey);
    
    if (cachedData) {
      // 检查是否是空值标记
      if (cachedData ===
'NULL') {
        console.log('Null result cached for protection');
        return null;
      }
      return JSON.parse(cachedData);
    }
    
    // 查询数据库
    const userData = await getUserFromDatabase(userId);
    
    // 缓存结果，即使是null也缓存（但使用短TTL）
    if (userData) {
      await redisClient.set(cacheKey, JSON.stringify(userData), 'EX', 3600); // 1小时
    } else {
      await redisClient.set(cacheKey, 'NULL', 'EX', 60); // 1分钟短TTL
    }
    
    return userData;
  }
  
  // 布隆过滤器防穿透
  async getUserWithBloomFilter(userId) {
    const bloomFilter = await getBloomFilter('users');
    
    // 检查ID是否可能存在
    const mightExist = await bloomFilter.exists(userId);
    
    // 如果布隆过滤器说不存在，则一定不存在
    if (!mightExist) {
      console.log('Rejected by bloom filter');
      return null;
    }
    
    // 可能存在，检查缓存
    const cacheKey = `user:${userId}`;
    let userData = await redisClient.get(cacheKey);
    
    if (userData) {
      return JSON.parse(userData);
    }
    
    // 查询数据库
    userData = await getUserFromDatabase(userId);
    
    if (userData) {
      await redisClient.set(cacheKey, JSON.stringify(userData), 'EX', 3600);
    }
    
    return userData;
  }
}

// 6. 缓存击穿保护 - 互斥锁
class HotKeyProtection {
  constructor() {
    this.lockTimeout = 5000; // 5秒锁超时
    this.retryDelay = 100;   // 100ms重试间隔
    this.maxRetries = 20;    // 最多重试20次
  }
  
  // 获取分布式锁
  async acquireLock(lockKey, ttlMs) {
    // 使用 SET NX EX 实现分布式锁
    const token = crypto.randomBytes(16).toString('hex');
    const acquired = await redisClient.set(lockKey, token, 'NX', 'PX', ttlMs);
    return acquired === 'OK' ? token : null;
  }
  
  // 释放锁
  async releaseLock(lockKey, token) {
    // Lua脚本保证原子性
    const script = `
      if redis.call('get', KEYS[1]) == ARGV[1] then
        return redis.call('del', KEYS[1])
      else
        return 0
      end
    `;
    
    return await redisClient.eval(script, 1, lockKey, token);
  }
  
  // 防击穿的数据加载
  async getHotKey(key, dataLoader) {
    // 先尝试从缓存获取
    let data = await redisClient.get(key);
    
    if (data) {
      return JSON.parse(data);
    }
    
    // 缓存未命中，尝试获取锁
    const lockKey = `lock:${key}`;
    const lockToken = await this.acquireLock(lockKey, this.lockTimeout);
    
    if (lockToken) {
      try {
        // 双重检查，可能其他进程已经缓存了数据
        data = await redisClient.get(key);
        if (data) {
          return JSON.parse(data);
        }
        
        // 加载数据
        const freshData = await dataLoader();
        
        // 更新缓存
        if (freshData) {
          await redisClient.set(key, JSON.stringify(freshData), 'EX', 3600);
        }
        
        return freshData;
      } finally {
        // 释放锁
        await this.releaseLock(lockKey, lockToken);
      }
    } else {
      // 未获取到锁，等待其他进程加载数据
      for (let i = 0; i < this.maxRetries; i++) {
        await new Promise(resolve => setTimeout(resolve, this.retryDelay));
        
        // 重新尝试获取缓存
        data = await redisClient.get(key);
        if (data) {
          return JSON.parse(data);
        }
      }
      
      // 最终还是失败，直接加载数据不经过缓存
      return await dataLoader();
    }
  }
}

// 7. 缓存雪崩保护 - 随机TTL
class CacheAvoidAvalanche {
  async set(key, data, baseTTL = 3600) {
    // 添加随机抖动，避免同时过期
    const jitter = Math.floor(Math.random() * 300); // 0-300秒随机抖动
    const ttl = baseTTL + jitter;
    
    await redisClient.set(key, JSON.stringify(data), 'EX', ttl);
    return data;
  }
  
  // 缓存预热
  async warmupCache(keys, dataLoader) {
    for (const key of keys) {
      try {
        const data = await dataLoader(key);
        if (data) {
          await this.set(key, data);
          console.log(`Preloaded cache for ${key}`);
        }
      } catch (error) {
        console.error(`Failed to preload cache for ${key}:`, error);
      }
    }
  }
  
  // 定期刷新热点数据
  startRefreshTimer(keys, dataLoader, intervalMs = 1800000) { // 30分钟
    return setInterval(async () => {
      for (const key of keys) {
        try {
          // 获取当前TTL
          const ttl = await redisClient.ttl(key);
          
          // 如果TTL低于阈值，刷新数据
          if (ttl !== -1 && ttl < 600) { // 10分钟
            const data = await dataLoader(key);
            if (data) {
              await this.set(key, data);
              console.log(`Refreshed cache for ${key}`);
            }
          }
        } catch (error) {
          console.error(`Failed to refresh cache for ${key}:`, error);
        }
      }
    }, intervalMs);
  }
}
```

**缓存策略特点**：

- Cache-Aside: 应用管理缓存更新，简单灵活
- Read-Through: 缓存库自动加载数据，简化应用逻辑
- Write-Through: 同时更新缓存和数据库，保持一致性
- Write-Behind: 异步批量更新数据库，提高性能
- 穿透保护: 避免无效查询压垮数据库
- 击穿保护: 防止热点数据同时失效导致数据库压力
- 雪崩保护: 避免大量缓存同时过期

-**缓存系统比较**

|特性|Redis|Memcached|本地内存缓存|CDN缓存|
|---|---|---|---|---|
|数据结构|丰富|简单K/V|灵活|文件/对象|
|持久化|支持|无|取决于实现|边缘存储|
|分布式|原生支持|客户端分片|单机|全球分布|
|过期策略|多种|简单|实现相关|可配置|
|事务|支持|无|可实现|无|
|最大值大小|512MB|1MB|内存限制|大文件支持|
|性能|极高|极高|最高|网络相关|
|应用场景|多功能缓存|简单高速缓存|热点数据|静态资源|

## 5. 全栈架构模式

### 5.1 JAMStack架构

现代JAMStack架构采用静态生成与API组合：

```javascript
// Next.js JAMStack实现示例

// 静态站点生成 - pages/blog/[slug].js
export async function getStaticPaths() {
  // 在构建时获取所有可能的博客文章路径
  const posts = await api.getAllPostSlugs();
  
  return {
    paths: posts.map(post => ({ params: { slug: post.slug } })),
    fallback: 'blocking' // 对新内容进行SSR
  };
}

export async function getStaticProps({ params }) {
  // 获取特定博文的数据
  const post = await api.getPostBySlug(params.slug);
  
  // 如果没有找到内容，返回404
  if (!post) {
    return { notFound: true };
  }
  
  // MDX编译
  const mdxSource = await serializeMarkdown(post.content);
  
  return {
    props: {
      post,
      mdxSource
    },
    // 增量静态再生成 - 每小时重新生成
    revalidate: 3600
  };
}

// React组件渲染静态内容
export default function BlogPost({ post, mdxSource }) {
  return (
    <Layout>
      <article>
        <Head>
          <title>{post.title} | My Blog</title>
          <meta name="description" content={post.excerpt} />
          <meta property="og:image" content={post.coverImage} />
        </Head>
        
        <header>
          <h1>{post.title}</h1>
          <time dateTime={post.date}>{formatDate(post.date)}</time>
          {post.author && <Author author={post.author} />}
        </header>
        
        <MDXRemote {...mdxSource} components={MDXComponents} />
        
        <footer>
          <TagList tags={post.tags} />
          <ShareButtons url={`/blog/${post.slug}`} title={post.title} />
        </footer>
      </article>
      
      <RelatedPosts currentPostId={post.id} tags={post.tags} />
    </Layout>
  );
}

// 客户端API调用 - 添加评论功能
function CommentSection({ postId }) {
  const [comments, setComments] = useState([]);
  const [isLoading, setIsLoading] = useState(true);
  const [newComment, setNewComment] = useState('');
  
  // 加载评论
  useEffect(() => {
    async function loadComments() {
      try {
        setIsLoading(true);
        const data = await fetch(`/api/comments?postId=${postId}`).then(r => r.json());
        setComments(data);
      } catch (error) {
        console.error('Failed to load comments:', error);
      } finally {
        setIsLoading(false);
      }
    }
    
    loadComments();
  }, [postId]);
  
  // 提交评论
  async function handleSubmit(e) {
    e.preventDefault();
    if (!newComment.trim()) return;
    
    try {
      const response = await fetch('/api/comments', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({ postId, content: newComment })
      });
      
      if (response.ok) {
        const comment = await response.json();
        setComments(prev => [...prev, comment]);
        setNewComment('');
      }
    } catch (error) {
      console.error('Failed to submit comment:', error);
    }
  }
  
  return (
    <section>
      <h3>Comments ({comments.length})</h3>
      
      {isLoading ? (
        <p>Loading comments...</p>
      ) : (
        <ul>
          {comments.map(comment => (
            <li key={comment.id}>
              <p>{comment.content}</p>
              <footer>
                <span>{comment.author}</span>
                <time>{formatDate(comment.createdAt)}</time>
              </footer>
            </li>
          ))}
        </ul>
      )}
      
      <form onSubmit={handleSubmit}>
        <textarea
          value={newComment}
          onChange={e => setNewComment(e.target.value)}
          placeholder="Add a comment..."
          required
        />
        <button type="submit">Post Comment</button>
      </form>
    </section>
  );
}

// API路由 - pages/api/comments.js
export default async function handler(req, res) {
  // GET请求 - 获取评论
  if (req.method === 'GET') {
    const { postId } = req.query;
    
    try {
      const comments = await db.comments.findMany({
        where: { postId },
        orderBy: { createdAt: 'desc' }
      });
      
      return res.status(200).json(comments);
    } catch (error) {
      console.error('Failed to fetch comments:', error);
      return res.status(500).json({ message: 'Failed to fetch comments' });
    }
  }
  
  // POST请求 - 创建评论
  if (req.method === 'POST') {
    const { postId, content } = req.body;
    
    // 身份验证
    const session = await getSession({ req });
    if (!session) {
      return res.status(401).json({ message: 'Unauthorized' });
    }
    
    try {
      const comment = await db.comments.create({
        data: {
          postId,
          content,
          authorId: session.user.id
        }
      });
      
      return res.status(201).json(comment);
    } catch (error) {
      console.error('Failed to create comment:', error);
      return res.status(500).json({ message: 'Failed to create comment' });
    }
  }
  
  // 其他HTTP方法不支持
  return res.status(405).json({ message: 'Method not allowed' });
}
```

-**JAMStack部署配置 - Netlify**

```toml
# netlify.toml
[build]
  command = "npm run build"
  publish = "out"
  functions = "netlify/functions"

[build.environment]
  NODE_VERSION = "16"
  NPM_FLAGS = "--silent"

# 增量静态重新生成处理
[[plugins]]
  package = "@netlify/plugin-nextjs"

# 重定向和重写
[[redirects]]
  from = "/api/*"
  to = "/.netlify/functions/:splat"
  status = 200

# 缓存控制
[[headers]]
  for = "/_next/static/*"
  [headers.values]
    Cache-Control = "public, max-age=31536000, immutable"

[[headers]]
  for = "/images/*"
  [headers.values]
    Cache-Control = "public, max-age=604800"

# 环境变量根据部署环境
[context.production.environment]
  NEXT_PUBLIC_API_URL = "https://api.example.com"
  
[context.deploy-preview.environment]
  NEXT_PUBLIC_API_URL = "https://staging-api.example.com"
```

**JAMStack架构特点**：

- 预渲染HTML提供极快的首屏加载
- 基于API的功能动态化
- CDN分发确保全球快速访问
- 头部CMS与静态生成分离
- 无服务器函数处理动态需求
- 增量静态再生成平衡静态与动态

### 5.2 MERN/MEAN/PERN栈

-**MERN栈架构**

MongoDB + Express + React + Node.js 栈架构示例：

```javascript
// MERN栈示例 - 简化版电子商务应用

// 后端 - Express API
// app.js
const express = require('express');
const mongoose = require('mongoose');
const cors = require('cors');
const morgan = require('morgan');
const helmet = require('helmet');
const rateLimit = require('express-rate-limit');
const compression = require('compression');
const { authenticateJWT } = require('./middleware/auth');

// 初始化Express
const app = express();

// 中间件
app.use(cors());
app.use(express.json());
app.use(morgan('combined'));
app.use(helmet());
app.use(compression());

// 速率限制
const apiLimiter = rateLimit({
  windowMs: 15 * 60 * 1000, // 15分钟
  max: 100 // 每IP限制请求数
});
app.use('/api/', apiLimiter);

// 数据库连接
mongoose.connect(process.env.MONGO_URI, {
  useNewUrlParser: true,
  useUnifiedTopology: true,
  useCreateIndex: true
})
.then(() => console.log('MongoDB connected'))
.catch(err => console.error('MongoDB connection error:', err));

// 路由
app.use('/api/auth', require('./routes/auth'));
app.use('/api/products', require('./routes/products'));
app.use('/api/orders', authenticateJWT, require('./routes/orders'));
app.use('/api/users', authenticateJWT, require('./routes/users'));

// 错误处理
app.use((err, req, res, next) => {
  console.error(err.stack);
  res.status(err.status || 500).json({
    message: err.message,
    error: process.env.NODE_ENV === 'development' ? err : {}
  });
});

// 启动服务器
const PORT = process.env.PORT || 5000;
app.listen(PORT, () => console.log(`Server running on port ${PORT}`));

// 产品模型 - models/Product.js
const mongoose = require('mongoose');

const productSchema = new mongoose.Schema({
  name: {
    type: String,
    required: true,
    trim: true
  },
  description: {
    type: String,
    required: true
  },
  price: {
    type: Number,
    required: true,
    min: 0
  },
  category: {
    type: String,
    required: true,
    enum: ['electronics', 'clothing', 'books', 'home', 'other']
  },
  imageUrl: String,
  stock: {
    type: Number,
    required: true,
    min: 0,
    default: 0
  },
  ratings: [{
    user: {
      type: mongoose.Schema.Types.ObjectId,
      ref: 'User'
    },
    rating: {
      type: Number,
      min: 1,
      max: 5,
      required: true
    },
    review: String,
    date: {
      type: Date,
      default: Date.now
    }
  }],
  featured: {
    type: Boolean,
    default: false
  }
}, {
  timestamps: true
});

// 计算平均评分的虚拟属性
productSchema.virtual('averageRating').get(function() {
  if (this.ratings.length === 0) return 0;
  
  const sum = this.ratings.reduce((total, r) => total + r.rating, 0);
  return sum / this.ratings.length;
});

// 确保虚拟属性包含在JSON输出
productSchema.set('toJSON', { virtuals: true });
productSchema.set('toObject', { virtuals: true });

// 添加索引
productSchema.index({ name: 'text', description: 'text' });
productSchema.index({ category: 1 });
productSchema.index({ price: 1 });

const Product = mongoose.model('Product', productSchema);

module.exports = Product;

// 产品路由 - routes/products.js
const express = require('express');
const router = express.Router();
const Product = require('../models/Product');
const { authenticateJWT, authorizeAdmin } = require('../middleware/auth');
const { validateProduct } = require('../middleware/validation');

// 获取所有产品 (公开)
router.get('/', async (req, res) => {
  try {
    const { 
      category, 
      minPrice, 
      maxPrice, 
      sortBy = 'createdAt', 
      sortOrder = 'desc',
      page = 1,
      limit = 10,
      search
    } = req.query;
    
    const query = {};
    
    // 过滤条件
    if (category) query.category = category;
    if (minPrice !== undefined) query.price = { $gte: parseFloat(minPrice) };
    if (maxPrice !== undefined) {
      query.price = query.price || {};
      query.price.$lte = parseFloat(maxPrice);
    }
    if (search) {
      query.$text = { $search: search };
    }
    
    // 添加分页
    const skip = (parseInt(page) - 1) * parseInt(limit);
    
    // 执行查询
    const products = await Product.find(query)
      .sort({ [sortBy]: sortOrder === 'asc' ? 1 : -1 })
      .skip(skip)
      .limit(parseInt(limit));
    
    // 获取总数
    const total = await Product.countDocuments(query);
    
    res.json({
      products,
      pagination: {
        total,
        page: parseInt(page),
        pages: Math.ceil(total / parseInt(limit))
      }
    });
  } catch (err) {
    res.status(500).json({ message: err.message });
  }
});

// 获取单个产品 (公开)
router.get('/:id', async (req, res) => {
  try {
    const product = await Product.findById(req.params.id)
      .populate('ratings.user', 'name');
    
    if (!product) {
      return res.status(404).json({ message: 'Product not found' });
    }
    
    res.json(product);
  } catch (err) {
    res.status(500).json({ message: err.message });
  }
});

// 创建产品 (仅管理员)
router.post('/', [authenticateJWT, authorizeAdmin, validateProduct], async (req, res) => {
  try {
    const newProduct = new Product(req.body);
    const savedProduct = await newProduct.save();
    res.status(201).json(savedProduct);
  } catch (err) {
    res.status(400).json({ message: err.message });
  }
});

// 更新产品 (仅管理员)
router.put('/:id', [authenticateJWT, authorizeAdmin, validateProduct], async (req, res) => {
  try {
    const updatedProduct = await Product.findByIdAndUpdate(
      req.params.id,
      req.body,
      { new: true, runValidators: true }
    );
    
    if (!updatedProduct) {
      return res.status(404).json({ message: 'Product not found' });
    }
    
    res.json(updatedProduct);
  } catch (err) {
    res.status(400).json({ message: err.message });
  }
});

// 删除产品 (仅管理员)
router.delete('/:id', [authenticateJWT, authorizeAdmin], async (req, res) => {
  try {
    const deletedProduct = await Product.findByIdAndDelete(req.params.id);
    
    if (!deletedProduct) {
      return res.status(404).json({ message: 'Product not found' });
    }
    
    res.json({ message: 'Product deleted successfully' });
  } catch (err) {
    res.status(500).json({ message: err.message });
  }
});

// 添加产品评价
router.post('/:id/ratings', authenticateJWT, async (req, res) => {
  try {
    const { rating, review } = req.body;
    const product = await Product.findById(req.params.id);
    
    if (!product) {
      return res.status(404).json({ message: 'Product not found' });
    }
    
    // 检查用户是否已评价
    const existingRating = product.ratings.find(
      r => r.user.toString() === req.user.id
    );
    
    if (existingRating) {
      return res.status(400).json({ message: 'You already rated this product' });
    }
    
    product.ratings.push({
      user: req.user.id,
      rating,
      review
    });
    
    await product.save();
    
    res.status(201).json(product);
  } catch (err) {
    res.status(400).json({ message: err.message });
  }
});

module.exports = router;
```

-**React前端 - 组件结构**

```jsx
// MERN栈前端 - React与Redux

// src/redux/store.js
import { configureStore } from '@reduxjs/toolkit';
import { setupListeners } from '@reduxjs/toolkit/query/react';
import authReducer from './slices/authSlice';
import cartReducer from './slices/cartSlice';
import { productsApi } from './services/productsApi';
import { ordersApi } from './services/ordersApi';

export const store = configureStore({
  reducer: {
    auth: authReducer,
    cart: cartReducer,
    [productsApi.reducerPath]: productsApi.reducer,
    [ordersApi.reducerPath]: ordersApi.reducer
  },
  middleware: (getDefaultMiddleware) =>
    getDefaultMiddleware()
      .concat(productsApi.middleware)
      .concat(ordersApi.middleware)
});

setupListeners(store.dispatch);

// src/redux/services/productsApi.js
import { createApi, fetchBaseQuery } from '@reduxjs/toolkit/query/react';

export const productsApi = createApi({
  reducerPath: 'productsApi',
  baseQuery: fetchBaseQuery({ 
    baseUrl: '/api/products',
    prepareHeaders: (headers, { getState }) => {
      const token = getState().auth.token;
      if (token) {
        headers.set('authorization', `Bearer ${token}`);
      }
      return headers;
    }
  }),
  tagTypes: ['Product'],
  endpoints: (builder) => ({
    getProducts: builder.query({
      query: (params) => ({
        url: '',
        params
      }),
      providesTags: (result) =>
        result
          ? [
              ...result.products.map(({ id }) => ({ type: 'Product', id })),
              { type: 'Product', id: 'LIST' }
            ]
          : [{ type: 'Product', id: 'LIST' }]
    }),
    getProductById: builder.query({
      query: (id) => `/${id}`,
      providesTags: (result, error, id) => [{ type: 'Product', id }]
    }),
    addProduct: builder.mutation({
      query: (product) => ({
        url: '',
        method: 'POST',
        body: product
      }),
      invalidatesTags: [{ type: 'Product', id: 'LIST' }]
    }),
    updateProduct: builder.mutation({
      query: ({ id, ...product }) => ({
        url: `/${id}`,
        method: 'PUT',
        body: product
      }),
      invalidatesTags: (result, error, { id }) => [{ type: 'Product', id }]
    }),
    deleteProduct: builder.mutation({
      query: (id) => ({
        url: `/${id}`,
        method: 'DELETE'
      }),
      invalidatesTags: [{ type: 'Product', id: 'LIST' }]
    }),
    addRating: builder.mutation({
      query: ({ id, rating, review }) => ({
        url: `/${id}/ratings`,
        method: 'POST',
        body: { rating, review }
      }),
      invalidatesTags: (result, error, { id }) => [{ type: 'Product', id }]
    })
  })
});

export const {
  useGetProductsQuery,
  useGetProductByIdQuery,
  useAddProductMutation,
  useUpdateProductMutation,
  useDeleteProductMutation,
  useAddRatingMutation
} = productsApi;

// src/components/ProductDetail.jsx
import React from 'react';
import { useParams, useNavigate } from 'react-router-dom';
import { useSelector } from 'react-redux';
import { 
  useGetProductByIdQuery,
  useAddRatingMutation
} from '../redux/services/productsApi';
import { addToCart } from '../redux/slices/cartSlice';
import { useDispatch } from 'react-redux';
import {
  Box,
  Button,
  Grid,
  Typography,
  Rating,
  Divider,
  TextField,
  Card,
  CardContent,
  Alert,
  CircularProgress,
  Snackbar
} from '@mui/material';

const ProductDetail = () => {
  const { id } = useParams();
  const navigate = useNavigate();
  const dispatch = useDispatch();
  const { isAuthenticated } = useSelector((state) => state.auth);
  
  const [userRating, setUserRating] = React.useState(0);
  const [userReview, setUserReview] = React.useState('');
  const [snackbar, setSnackbar] = React.useState({
    open: false,
    message: '',
    severity: 'success'
  });
  
  const { data: product, isLoading, error } = useGetProductByIdQuery(id);
  const [addRating, { isLoading: isRatingLoading }] = useAddRatingMutation();
  
  if (isLoading) {
    return <CircularProgress />;
  }
  
  if (error) {
    return (
      <Alert severity="error">
        Error loading product: {error.data?.message || error.error}
      </Alert>
    );
  }
  
  if (!product) {
    return <Alert severity="warning">Product not found
.</Alert>;
  }
  
  const handleAddToCart = () => {
    dispatch(addToCart({
      id: product._id,
      name: product.name,
      price: product.price,
      imageUrl: product.imageUrl,
      quantity: 1
    }));
    
    setSnackbar({
      open: true,
      message: 'Product added to cart!',
      severity: 'success'
    });
  };
  
  const handleSubmitReview = async () => {
    if (!isAuthenticated) {
      navigate('/login', { state: { from: `/products/${id}` } });
      return;
    }
    
    try {
      await addRating({ id, rating: userRating, review: userReview }).unwrap();
      setUserRating(0);
      setUserReview('');
      setSnackbar({
        open: true,
        message: 'Thank you for your review!',
        severity: 'success'
      });
    } catch (err) {
      setSnackbar({
        open: true,
        message: err.data?.message || 'Failed to submit review',
        severity: 'error'
      });
    }
  };
  
  const handleCloseSnackbar = () => {
    setSnackbar({ ...snackbar, open: false });
  };
  
  return (
    <Box sx={{ padding: 3 }}>
      <Grid container spacing={4}>
        <Grid item xs={12} md={6}>
          <img 
            src={product.imageUrl || '/placeholder.png'} 
            alt={product.name}
            style={{ width: '100%', borderRadius: 8 }}
          />
        </Grid>
        
        <Grid item xs={12} md={6}>
          <Typography variant="h4" gutterBottom>
            {product.name}
          </Typography>
          
          <Box display="flex" alignItems="center" mb={2}>
            <Rating value={product.averageRating} precision={0.5} readOnly />
            <Typography variant="body2" ml={1}>
              ({product.ratings.length} reviews)
            </Typography>
          </Box>
          
          <Typography variant="h5" color="primary" gutterBottom>
            ${product.price.toFixed(2)}
          </Typography>
          
          <Typography variant="body1" paragraph>
            {product.description}
          </Typography>
          
          <Box display="flex" alignItems="center" mb={3}>
            <Typography variant="subtitle1" mr={2}>
              Status:
            </Typography>
            {product.stock > 0 ? (
              <Typography variant="body1" color="success.main">
                In Stock ({product.stock} available)
              </Typography>
            ) : (
              <Typography variant="body1" color="error">
                Out of Stock
              </Typography>
            )}
          </Box>
          
          <Button 
            variant="contained" 
            color="primary" 
            size="large"
            onClick={handleAddToCart}
            disabled={product.stock === 0}
            fullWidth
          >
            Add to Cart
          </Button>
        </Grid>
      </Grid>
      
      <Divider sx={{ my: 4 }} />
      
      <Box mb={4}>
        <Typography variant="h5" gutterBottom>
          Product Reviews
        </Typography>
        
        {product.ratings.length > 0 ? (
          <Grid container spacing={2}>
            {product.ratings.map((rating) => (
              <Grid item xs={12} key={rating._id}>
                <Card>
                  <CardContent>
                    <Box display="flex" justifyContent="space-between" alignItems="center">
                      <Typography variant="subtitle1">
                        {rating.user.name}
                      </Typography>
                      <Rating value={rating.rating} readOnly />
                    </Box>
                    <Typography variant="body2" color="text.secondary">
                      {new Date(rating.date).toLocaleDateString()}
                    </Typography>
                    <Typography variant="body1" mt={1}>
                      {rating.review}
                    </Typography>
                  </CardContent>
                </Card>
              </Grid>
            ))}
          </Grid>
        ) : (
          <Typography>No reviews yet. Be the first to review this product!</Typography>
        )}
      </Box>
      
      <Box>
        <Typography variant="h5" gutterBottom>
          Write a Review
        </Typography>
        
        {!isAuthenticated && (
          <Alert severity="info" sx={{ mb: 2 }}>
            Please <Button onClick={() => navigate('/login')}>log in</Button> to write a review.
          </Alert>
        )}
        
        <Box component="form" noValidate sx={{ mt: 1 }}>
          <Box display="flex" alignItems="center" mb={2}>
            <Typography mr={2}>Your Rating:</Typography>
            <Rating
              value={userRating}
              onChange={(e, newValue) => setUserRating(newValue)}
            />
          </Box>
          
          <TextField
            fullWidth
            multiline
            rows={4}
            label="Your Review"
            value={userReview}
            onChange={(e) => setUserReview(e.target.value)}
            disabled={!isAuthenticated}
            margin="normal"
          />
          
          <Button
            variant="contained"
            onClick={handleSubmitReview}
            disabled={!isAuthenticated || userRating === 0 || isRatingLoading}
            sx={{ mt: 2 }}
          >
            {isRatingLoading ? <CircularProgress size={24} /> : 'Submit Review'}
          </Button>
        </Box>
      </Box>
      
      <Snackbar
        open={snackbar.open}
        autoHideDuration={6000}
        onClose={handleCloseSnackbar}
      >
        <Alert onClose={handleCloseSnackbar} severity={snackbar.severity}>
          {snackbar.message}
        </Alert>
      </Snackbar>
    </Box>
  );
};

export default ProductDetail;
```

**MERN架构特点**：

- JavaScript/TypeScript全栈开发
- MongoDB灵活数据模型支持快速迭代
- Express提供轻量级API框架
- React负责客户端用户界面
- Node.js统一后端运行时
- RESTful API或GraphQL连接前后端
- JWT实现无状态身份验证

-**PERN栈架构**

PostgreSQL + Express + React + Node.js 栈架构：

```javascript
// PERN栈示例 - 后端数据库模式
// db.js - 数据库连接
const { Pool } = require('pg');

const pool = new Pool({
  user: process.env.PG_USER,
  password: process.env.PG_PASSWORD,
  host: process.env.PG_HOST,
  port: process.env.PG_PORT,
  database: process.env.PG_DATABASE,
  ssl: process.env.NODE_ENV === 'production' ? { rejectUnauthorized: false } : false
});

module.exports = {
  query: (text, params) => pool.query(text, params)
};

// database.sql - 数据库模式定义
CREATE EXTENSION IF NOT EXISTS "uuid-ossp";

-- 用户表
CREATE TABLE users (
  id UUID PRIMARY KEY DEFAULT uuid_generate_v4(),
  name VARCHAR(100) NOT NULL,
  email VARCHAR(255) UNIQUE NOT NULL,
  password VARCHAR(255) NOT NULL,
  role VARCHAR(20) NOT NULL DEFAULT 'customer',
  created_at TIMESTAMP WITH TIME ZONE DEFAULT CURRENT_TIMESTAMP,
  updated_at TIMESTAMP WITH TIME ZONE DEFAULT CURRENT_TIMESTAMP
);

-- 产品表
CREATE TABLE products (
  id UUID PRIMARY KEY DEFAULT uuid_generate_v4(),
  name VARCHAR(255) NOT NULL,
  description TEXT NOT NULL,
  price DECIMAL(10, 2) NOT NULL CHECK (price >= 0),
  category VARCHAR(50) NOT NULL,
  image_url VARCHAR(512),
  stock INTEGER NOT NULL DEFAULT 0 CHECK (stock >= 0),
  featured BOOLEAN DEFAULT FALSE,
  created_at TIMESTAMP WITH TIME ZONE DEFAULT CURRENT_TIMESTAMP,
  updated_at TIMESTAMP WITH TIME ZONE DEFAULT CURRENT_TIMESTAMP
);

-- 订单表
CREATE TABLE orders (
  id UUID PRIMARY KEY DEFAULT uuid_generate_v4(),
  user_id UUID REFERENCES users(id) ON DELETE SET NULL,
  status VARCHAR(50) NOT NULL DEFAULT 'pending',
  total DECIMAL(10, 2) NOT NULL,
  shipping_address JSONB NOT NULL,
  payment_method VARCHAR(50) NOT NULL,
  created_at TIMESTAMP WITH TIME ZONE DEFAULT CURRENT_TIMESTAMP,
  updated_at TIMESTAMP WITH TIME ZONE DEFAULT CURRENT_TIMESTAMP
);

-- 订单项表
CREATE TABLE order_items (
  id UUID PRIMARY KEY DEFAULT uuid_generate_v4(),
  order_id UUID REFERENCES orders(id) ON DELETE CASCADE,
  product_id UUID REFERENCES products(id) ON DELETE SET NULL,
  quantity INTEGER NOT NULL CHECK (quantity > 0),
  price DECIMAL(10, 2) NOT NULL,
  created_at TIMESTAMP WITH TIME ZONE DEFAULT CURRENT_TIMESTAMP
);

-- 产品评价表
CREATE TABLE product_ratings (
  id UUID PRIMARY KEY DEFAULT uuid_generate_v4(),
  product_id UUID REFERENCES products(id) ON DELETE CASCADE,
  user_id UUID REFERENCES users(id) ON DELETE SET NULL,
  rating INTEGER NOT NULL CHECK (rating BETWEEN 1 AND 5),
  review TEXT,
  created_at TIMESTAMP WITH TIME ZONE DEFAULT CURRENT_TIMESTAMP
);

-- 索引
CREATE INDEX idx_products_category ON products(category);
CREATE INDEX idx_order_user ON orders(user_id);
CREATE INDEX idx_order_items_order ON order_items(order_id);
CREATE INDEX idx_product_ratings_product ON product_ratings(product_id);

-- 触发器函数 - 更新时间戳
CREATE OR REPLACE FUNCTION update_modified_column()
RETURNS TRIGGER AS $$
BEGIN
  NEW.updated_at = NOW();
  RETURN NEW;
END;
$$ LANGUAGE plpgsql;

-- 更新时间戳触发器
CREATE TRIGGER update_user_modtime
  BEFORE UPDATE ON users
  FOR EACH ROW EXECUTE PROCEDURE update_modified_column();

CREATE TRIGGER update_product_modtime
  BEFORE UPDATE ON products
  FOR EACH ROW EXECUTE PROCEDURE update_modified_column();

CREATE TRIGGER update_order_modtime
  BEFORE UPDATE ON orders
  FOR EACH ROW EXECUTE PROCEDURE update_modified_column();

-- 产品平均评分视图
CREATE VIEW product_average_ratings AS
SELECT 
  p.id,
  p.name,
  COALESCE(AVG(pr.rating), 0) AS average_rating,
  COUNT(pr.id) AS rating_count
FROM products p
LEFT JOIN product_ratings pr ON p.id = pr.product_id
GROUP BY p.id, p.name;

-- 产品库存函数
CREATE OR REPLACE FUNCTION decrease_product_stock(
  product_id_param UUID,
  quantity_param INTEGER
) RETURNS BOOLEAN AS $$
DECLARE
  current_stock INTEGER;
BEGIN
  -- 查询当前库存
  SELECT stock INTO current_stock FROM products WHERE id = product_id_param;
  
  -- 检查库存是否足够
  IF current_stock >= quantity_param THEN
    -- 减少库存
    UPDATE products SET stock = stock - quantity_param WHERE id = product_id_param;
    RETURN TRUE;
  ELSE
    RETURN FALSE;
  END IF;
END;
$$ LANGUAGE plpgsql;

// 产品路由处理 - routes/products.js
const router = require('express').Router();
const db = require('../db');
const { authenticateJWT, authorizeAdmin } = require('../middleware/auth');
const { validateProduct } = require('../middleware/validation');

// 获取所有产品
router.get('/', async (req, res) => {
  try {
    const { category, minPrice, maxPrice, sortBy = 'created_at', sortOrder = 'DESC', page = 1, limit = 10 } = req.query;
    
    let query = `
      SELECT p.*, COALESCE(pr.average_rating, 0) as average_rating, COALESCE(pr.rating_count, 0) as rating_count
      FROM products p
      LEFT JOIN product_average_ratings pr ON p.id = pr.id
      WHERE 1=1
    `;
    
    const queryParams = [];
    let paramIndex = 1;
    
    if (category) {
      query += ` AND p.category = $${paramIndex}`;
      queryParams.push(category);
      paramIndex++;
    }
    
    if (minPrice !== undefined) {
      query += ` AND p.price >= $${paramIndex}`;
      queryParams.push(minPrice);
      paramIndex++;
    }
    
    if (maxPrice !== undefined) {
      query += ` AND p.price <= $${paramIndex}`;
      queryParams.push(maxPrice);
      paramIndex++;
    }
    
    // 获取总数
    const countQuery = `SELECT COUNT(*) FROM (${query}) AS count_query`;
    const countResult = await db.query(countQuery, queryParams);
    const total = parseInt(countResult.rows[0].count);
    
    // 添加排序和分页
    const validSortColumns = ['name', 'price', 'created_at', 'average_rating'];
    const actualSortBy = validSortColumns.includes(sortBy) ? sortBy : 'created_at';
    const actualSortOrder = sortOrder.toUpperCase() === 'ASC' ? 'ASC' : 'DESC';
    
    query += ` ORDER BY p.${actualSortBy} ${actualSortOrder}`;
    
    const offset = (parseInt(page) - 1) * parseInt(limit);
    query += ` LIMIT $${paramIndex} OFFSET $${paramIndex + 1}`;
    queryParams.push(parseInt(limit), offset);
    
    const result = await db.query(query, queryParams);
    
    res.json({
      products: result.rows,
      pagination: {
        total,
        page: parseInt(page),
        pages: Math.ceil(total / parseInt(limit))
      }
    });
  } catch (err) {
    console.error(err);
    res.status(500).json({ message: 'Server error' });
  }
});

// 获取单个产品
router.get('/:id', async (req, res) => {
  try {
    // 获取产品详情
    const productQuery = `
      SELECT p.*, COALESCE(pr.average_rating, 0) as average_rating, COALESCE(pr.rating_count, 0) as rating_count
      FROM products p
      LEFT JOIN product_average_ratings pr ON p.id = pr.id
      WHERE p.id = $1
    `;
    const productResult = await db.query(productQuery, [req.params.id]);
    
    if (productResult.rows.length === 0) {
      return res.status(404).json({ message: 'Product not found' });
    }
    
    const product = productResult.rows[0];
    
    // 获取产品评价
    const ratingsQuery = `
      SELECT pr.*, u.name as user_name
      FROM product_ratings pr
      JOIN users u ON pr.user_id = u.id
      WHERE pr.product_id = $1
      ORDER BY pr.created_at DESC
    `;
    const ratingsResult = await db.query(ratingsQuery, [req.params.id]);
    
    // 组合结果
    product.ratings = ratingsResult.rows;
    
    res.json(product);
  } catch (err) {
    console.error(err);
    res.status(500).json({ message: 'Server error' });
  }
});

// 创建产品 (管理员)
router.post('/', [authenticateJWT, authorizeAdmin, validateProduct], async (req, res) => {
  try {
    const { name, description, price, category, imageUrl, stock, featured } = req.body;
    
    const query = `
      INSERT INTO products (name, description, price, category, image_url, stock, featured)
      VALUES ($1, $2, $3, $4, $5, $6, $7)
      RETURNING *
    `;
    
    const result = await db.query(query, [
      name, 
      description, 
      price, 
      category, 
      imageUrl || null, 
      stock || 0, 
      featured || false
    ]);
    
    res.status(201).json(result.rows[0]);
  } catch (err) {
    console.error(err);
    res.status(500).json({ message: 'Server error' });
  }
});

// 更新产品 (管理员)
router.put('/:id', [authenticateJWT, authorizeAdmin, validateProduct], async (req, res) => {
  try {
    const { name, description, price, category, imageUrl, stock, featured } = req.body;
    
    const query = `
      UPDATE products
      SET name = $1, description = $2, price = $3, category = $4,
          image_url = $5, stock = $6, featured = $7
      WHERE id = $8
      RETURNING *
    `;
    
    const result = await db.query(query, [
      name,
      description,
      price,
      category,
      imageUrl || null,
      stock || 0,
      featured || false,
      req.params.id
    ]);
    
    if (result.rows.length === 0) {
      return res.status(404).json({ message: 'Product not found' });
    }
    
    res.json(result.rows[0]);
  } catch (err) {
    console.error(err);
    res.status(500).json({ message: 'Server error' });
  }
});

// 添加产品评价
router.post('/:id/ratings', authenticateJWT, async (req, res) => {
  try {
    const { rating, review } = req.body;
    const productId = req.params.id;
    const userId = req.user.id;
    
    // 验证产品存在
    const productCheck = await db.query('SELECT id FROM products WHERE id = $1', [productId]);
    if (productCheck.rows.length === 0) {
      return res.status(404).json({ message: 'Product not found' });
    }
    
    // 检查用户是否已评价
    const existingRating = await db.query(
      'SELECT id FROM product_ratings WHERE product_id = $1 AND user_id = $2',
      [productId, userId]
    );
    
    if (existingRating.rows.length > 0) {
      return res.status(400).json({ message: 'You already rated this product' });
    }
    
    // 添加新评价
    const query = `
      INSERT INTO product_ratings (product_id, user_id, rating, review)
      VALUES ($1, $2, $3, $4)
      RETURNING *
    `;
    
    const result = await db.query(query, [productId, userId, rating, review || null]);
    
    res.status(201).json(result.rows[0]);
  } catch (err) {
    console.error(err);
    res.status(500).json({ message: 'Server error' });
  }
});

module.exports = router;
```

**PERN栈架构特点**：

- PostgreSQL提供强大的关系型数据能力
- 事务保证数据一致性
- SQL提供强大的查询能力
- 视图和存储过程支持复杂业务逻辑
- 触发器用于自动化操作
- 与MERN架构类似的前端结构

### 5.3 云原生应用架构

-**云原生电子商务应用架构**

```yaml
# Kubernetes配置示例 - 电子商务微服务应用

# 产品服务部署
apiVersion: apps/v1
kind: Deployment
metadata:
  name: product-service
  namespace: ecommerce
spec:
  replicas: 3
  selector:
    matchLabels:
      app: product-service
  template:
    metadata:
      labels:
        app: product-service
    spec:
      containers:
      - name: product-service
        image: ecommerce/product-service:v1.2.3
        ports:
        - containerPort: 8080
        env:
        - name: SPRING_PROFILES_ACTIVE
          value: "production"
        - name: DB_HOST
          valueFrom:
            configMapKeyRef:
              name: ecommerce-config
              key: postgres.host
        - name: DB_NAME
          valueFrom:
            configMapKeyRef:
              name: ecommerce-config
              key: postgres.database
        - name: DB_USER
          valueFrom:
            secretKeyRef:
              name: db-credentials
              key: username
        - name: DB_PASSWORD
          valueFrom:
            secretKeyRef:
              name: db-credentials
              key: password
        resources:
          requests:
            memory: "512Mi"
            cpu: "250m"
          limits:
            memory: "1Gi"
            cpu: "500m"
        livenessProbe:
          httpGet:
            path: /actuator/health/liveness
            port: 8080
          initialDelaySeconds: 60
          periodSeconds: 15
        readinessProbe:
          httpGet:
            path: /actuator/health/readiness
            port: 8080
          initialDelaySeconds: 30
          periodSeconds: 10
        volumeMounts:
        - name: config-volume
          mountPath: /app/config
      volumes:
      - name: config-volume
        configMap:
          name: product-service-config
      imagePullSecrets:
      - name: registry-credentials

# 产品服务 Service
apiVersion: v1
kind: Service
metadata:
  name: product-service
  namespace: ecommerce
spec:
  selector:
    app: product-service
  ports:
  - port: 80
    targetPort: 8080
  type: ClusterIP

# API Gateway
apiVersion: networking.istio.io/v1alpha3
kind: Gateway
metadata:
  name: ecommerce-gateway
  namespace: ecommerce
spec:
  selector:
    istio: ingressgateway
  servers:
  - port:
      number: 80
      name: http
      protocol: HTTP
    hosts:
    - "api.ecommerce.example.com"
    
# 路由配置
apiVersion: networking.istio.io/v1alpha3
kind: VirtualService
metadata:
  name: ecommerce-routes
  namespace: ecommerce
spec:
  hosts:
  - "api.ecommerce.example.com"
  gateways:
  - ecommerce-gateway
  http:
  - match:
    - uri:
        prefix: /api/products
    route:
    - destination:
        host: product-service
        port:
          number: 80
  - match:
    - uri:
        prefix: /api/orders
    route:
    - destination:
        host: order-service
        port:
          number: 80
  - match:
    - uri:
        prefix: /api/users
    route:
    - destination:
        host: user-service
        port:
          number: 80
  - match:
    - uri:
        prefix: /api/payments
    route:
    - destination:
        host: payment-service
        port:
          number: 80

# 服务网格策略 - 熔断
apiVersion: networking.istio.io/v1alpha3
kind: DestinationRule
metadata:
  name: product-service-circuit-breaker
  namespace: ecommerce
spec:
  host: product-service
  trafficPolicy:
    connectionPool:
      tcp:
        maxConnections: 100
      http:
        http1MaxPendingRequests: 25
        maxRequestsPerConnection: 10
    outlierDetection:
      consecutiveErrors: 5
      interval: 30s
      baseEjectionTime: 30s
      maxEjectionPercent: 100

# HorizontalPodAutoscaler
apiVersion: autoscaling/v2
kind: HorizontalPodAutoscaler
metadata:
  name: product-service-hpa
  namespace: ecommerce
spec:
  scaleTargetRef:
    apiVersion: apps/v1
    kind: Deployment
    name: product-service
  minReplicas: 2
  maxReplicas: 10
  metrics:
  - type: Resource
    resource:
      name: cpu
      target:
        type: Utilization
        averageUtilization: 70
  - type: Resource
    resource:
      name: memory
      target:
        type: Utilization
        averageUtilization: 80
  behavior:
    scaleDown:
      stabilizationWindowSeconds: 300
      policies:
      - type: Percent
        value: 100
        periodSeconds: 15

# 存储配置 - PVC
apiVersion: v1
kind: PersistentVolumeClaim
metadata:
  name: product-images-pvc
  namespace: ecommerce
spec:
  accessModes:
    - ReadWriteMany
  resources:
    requests:
      storage: 10Gi
  storageClassName: standard

# 定时任务 - 库存检查
apiVersion: batch/v1
kind: CronJob
metadata:
  name: inventory-check
  namespace: ecommerce
spec:
  schedule: "0 * * * *"  # 每小时执行一次
  concurrencyPolicy: Forbid
  jobTemplate:
    spec:
      template:
        spec:
          containers:
          - name: inventory-check
            image: ecommerce/inventory-job:v1.0.0
            env:
            - name: DB_HOST
              valueFrom:
                configMapKeyRef:
                  name: ecommerce-config
                  key: postgres.host
            - name: NOTIFICATION_SERVICE_URL
              value: "http://notification-service"
          restartPolicy: OnFailure

# 配置映射
apiVersion: v1
kind: ConfigMap
metadata:
  name: ecommerce-config
  namespace: ecommerce
data:
  postgres.host: "postgres-cluster.database"
  postgres.database: "ecommerce"
  elasticsearch.host: "elasticsearch-service.logging"
  redis.host: "redis-master.cache"
  kafka.bootstrap.servers: "kafka-headless.messaging:9092"

# 密钥
apiVersion: v1
kind: Secret
metadata:
  name: db-credentials
  namespace: ecommerce
type: Opaque
data:
  username: YWRtaW4=  # admin (base64编码)
  password: cEBzc3cwcmQ=  # p@ssw0rd (base64编码)
```

**云原生应用特点**：

- 容器化服务便于部署与扩展
- 微服务架构提高团队自主性
- 服务网格管理服务间通信
- 声明式API管理基础设施
- 自动扩展响应负载变化
- 配置与代码分离
- 不可变基础设施简化运维

### 5.4 服务网格与容器编排

-**服务网格架构 - Istio**

```yaml
# Istio服务网格配置示例

# 全局网络策略
apiVersion: networking.istio.io/v1beta1
kind: Sidecar
metadata:
  name: default
  namespace: ecommerce
spec:
  egress:
  - hosts:
    - "./*"
    - "istio-system/*"

# 互相TLS策略
apiVersion: security.istio.io/v1beta1
kind: PeerAuthentication
metadata:
  name: default
  namespace: ecommerce
spec:
  mtls:
    mode: STRICT

# 流量管理 - 金丝雀发布
apiVersion: networking.istio.io/v1alpha3
kind: VirtualService
metadata:
  name: product-service-canary
  namespace: ecommerce
spec:
  hosts:
  - product-service
  http:
  - name: "v2-routes"
    match:
    - headers:
        x-canary:
          exact: "true"
    route:
    - destination:
        host: product-service
        subset: v2
  - name: "v1-routes"
    route:
    - destination:
        host: product-service
        subset: v1

# 服务版本定义
apiVersion: networking.istio.io/v1alpha3
kind: DestinationRule
metadata:
  name: product-service-versions
  namespace: ecommerce
spec:
  host: product-service
  subsets:
  - name: v1
    labels:
      version: v1
  - name: v2
    labels:
      version: v2

# 请求路由 - 基于权重的流量分拆
apiVersion: networking.istio.io/v1alpha3
kind: VirtualService
metadata:
  name: product-service-rollout
  namespace: ecommerce
spec:
  hosts:
  - product-service
  http:
  - route:
    - destination:
        host: product-service
        subset: v1
      weight: 90
    - destination:
        host: product-service
        subset: v2
      weight: 10

# 服务容错 - 熔断器
apiVersion: networking.istio.io/v1alpha3
kind: DestinationRule
metadata:
  name: order-service-circuit-breaker
  namespace: ecommerce
spec:
  host: order-service
  trafficPolicy:
    connectionPool:
      tcp:
        maxConnections: 100
      http:
        http1MaxPendingRequests: 25
        maxRequestsPerConnection: 10
    outlierDetection:
      consecutiveErrors: 5
      interval: 30s
      baseEjectionTime: 30s
      maxEjectionPercent: 100

# 超时配置
apiVersion: networking.istio.io/v1alpha3
kind: VirtualService
metadata:
  name: payment-service-timeout
  namespace: ecommerce
spec:
  hosts:
  - payment-service
  http:
  - route:
    - destination:
        host: payment-service
    timeout: 3s

# 重试策略
apiVersion: networking.istio.io/v1alpha3
kind: VirtualService
metadata:
```yaml
  name: inventory-service-retry
  namespace: ecommerce
spec:
  hosts:
  - inventory-service
  http:
  - route:
    - destination:
        host: inventory-service
    retries:
      attempts: 3
      perTryTimeout: 500ms
      retryOn: connect-failure,refused-stream,unavailable,cancelled,deadline-exceeded,5xx

# 故障注入 - 用于测试恢复能力
apiVersion: networking.istio.io/v1alpha3
kind: VirtualService
metadata:
  name: shipping-service-fault-injection
  namespace: ecommerce-test
spec:
  hosts:
  - shipping-service
  http:
  - fault:
      delay:
        percentage:
          value: 25
        fixedDelay: 3s
      abort:
        percentage:
          value: 10
        httpStatus: 500
    route:
    - destination:
        host: shipping-service

# 认证策略
apiVersion: security.istio.io/v1beta1
kind: RequestAuthentication
metadata:
  name: jwt-auth
  namespace: ecommerce
spec:
  jwtRules:
  - issuer: "https://auth.ecommerce.example.com"
    jwksUri: "https://auth.ecommerce.example.com/.well-known/jwks.json"

# 授权策略
apiVersion: security.istio.io/v1beta1
kind: AuthorizationPolicy
metadata:
  name: payment-service-authz
  namespace: ecommerce
spec:
  selector:
    matchLabels:
      app: payment-service
  rules:
  - from:
    - source:
        principals: ["cluster.local/ns/ecommerce/sa/order-service"]
    to:
    - operation:
        methods: ["POST"]
        paths: ["/api/payments/process"]
  - from:
    - source:
        namespaces: ["ecommerce-admin"]
    to:
    - operation:
        methods: ["GET"]
        paths: ["/api/payments/*"]

# 遥测配置
apiVersion: telemetry.istio.io/v1alpha1
kind: Telemetry
metadata:
  name: ecommerce-telemetry
  namespace: ecommerce
spec:
  tracing:
    - providers:
        - name: jaeger
      randomSamplingPercentage: 10.0
  metrics:
    - providers:
        - name: prometheus
  accessLogging:
    - providers:
        - name: envoy
```

-**Kubernetes高级配置**

```yaml
# Kubernetes高级配置示例

# StatefulSet示例 - 数据库
apiVersion: apps/v1
kind: StatefulSet
metadata:
  name: postgres
  namespace: database
spec:
  serviceName: "postgres"
  replicas: 3
  selector:
    matchLabels:
      app: postgres
  template:
    metadata:
      labels:
        app: postgres
    spec:
      containers:
      - name: postgres
        image: postgres:14
        ports:
        - containerPort: 5432
          name: postgres
        env:
        - name: POSTGRES_USER
          valueFrom:
            secretKeyRef:
              name: postgres-secrets
              key: username
        - name: POSTGRES_PASSWORD
          valueFrom:
            secretKeyRef:
              name: postgres-secrets
              key: password
        - name: PGDATA
          value: /var/lib/postgresql/data/pgdata
        volumeMounts:
        - name: postgres-data
          mountPath: /var/lib/postgresql/data
  volumeClaimTemplates:
  - metadata:
      name: postgres-data
    spec:
      accessModes: [ "ReadWriteOnce" ]
      storageClassName: "premium-storage"
      resources:
        requests:
          storage: 100Gi

# Network Policies - 零信任网络模型
apiVersion: networking.k8s.io/v1
kind: NetworkPolicy
metadata:
  name: default-deny
  namespace: ecommerce
spec:
  podSelector: {}
  policyTypes:
  - Ingress
  - Egress

apiVersion: networking.k8s.io/v1
kind: NetworkPolicy
metadata:
  name: product-service-network-policy
  namespace: ecommerce
spec:
  podSelector:
    matchLabels:
      app: product-service
  policyTypes:
  - Ingress
  - Egress
  ingress:
  - from:
    - namespaceSelector:
        matchLabels:
          name: istio-system
    - podSelector:
        matchLabels:
          app: api-gateway
    ports:
    - protocol: TCP
      port: 8080
  egress:
  - to:
    - podSelector:
        matchLabels:
          app: postgres
    ports:
    - protocol: TCP
      port: 5432
  - to:
    - podSelector:
        matchLabels:
          app: redis
    ports:
    - protocol: TCP
      port: 6379
  - to:
    - namespaceSelector:
        matchLabels:
          name: monitoring
    ports:
    - protocol: TCP
      port: 9090

# Pod Security Context
apiVersion: v1
kind: Pod
metadata:
  name: secure-pod
  namespace: ecommerce
spec:
  securityContext:
    runAsUser: 1000
    runAsGroup: 3000
    fsGroup: 2000
  containers:
  - name: secure-container
    image: ecommerce/secure-app:v1
    securityContext:
      allowPrivilegeEscalation: false
      readOnlyRootFilesystem: true
      capabilities:
        drop:
          - ALL

# Pod Disruption Budget - 确保高可用性
apiVersion: policy/v1
kind: PodDisruptionBudget
metadata:
  name: product-service-pdb
  namespace: ecommerce
spec:
  minAvailable: 2  # 或 maxUnavailable: 1
  selector:
    matchLabels:
      app: product-service

# 资源配额
apiVersion: v1
kind: ResourceQuota
metadata:
  name: ecommerce-quota
  namespace: ecommerce
spec:
  hard:
    requests.cpu: "20"
    requests.memory: 20Gi
    limits.cpu: "40"
    limits.memory: 40Gi
    pods: "50"
    services: "30"
    persistentvolumeclaims: "20"

# 自定义资源定义 - Redis集群操作符
apiVersion: apiextensions.k8s.io/v1
kind: CustomResourceDefinition
metadata:
  name: redisclusters.cache.example.com
spec:
  group: cache.example.com
  names:
    kind: RedisCluster
    plural: redisclusters
    singular: rediscluster
    shortNames:
    - rdscl
  scope: Namespaced
  versions:
  - name: v1
    served: true
    storage: true
    schema:
      openAPIV3Schema:
        type: object
        properties:
          spec:
            type: object
            properties:
              replicas:
                type: integer
                minimum: 3
              version:
                type: string
              persistence:
                type: boolean
              resources:
                type: object
                properties:
                  requests:
                    type: object
                    properties:
                      memory:
                        type: string
                      cpu:
                        type: string
                  limits:
                    type: object
                    properties:
                      memory:
                        type: string
                      cpu:
                        type: string

# 使用自定义资源
apiVersion: cache.example.com/v1
kind: RedisCluster
metadata:
  name: ecommerce-cache
  namespace: cache
spec:
  replicas: 3
  version: "6.2"
  persistence: true
  resources:
    requests:
      memory: "1Gi"
      cpu: "500m"
    limits:
      memory: "2Gi"
      cpu: "1000m"
```

**服务网格与容器编排特点**：

- 服务网格提供统一的流量管理
- 零信任网络模型增强安全性
- 高级流量控制支持灰度发布
- 自动故障恢复与服务弹性
- 基于K8s的声明式资源管理
- 自定义资源扩展平台能力
- 细粒度资源控制与约束

## 6. 热门开源项目架构分析

### 6.1 VSCode架构解析

-**VSCode核心架构**

VSCode采用了独特的分层架构，结合Electron与浏览器技术：

```typescript
// VSCode架构示例代码 - 简化概念

// 1. 分层架构 - 核心部分

// 平台抽象层 - 提供跨平台API
interface IPlatformService {
  clipboard: IClipboardService;
  fileSystem: IFileSystemService;
  window: IWindowService;
  // 更多平台API...
}

// VSCode核心层 - 业务逻辑
class CoreComponent {
  constructor(
    @IInstantiationService private readonly instantiationService: IInstantiationService,
    @IPlatformService private readonly platformService: IPlatformService
  ) { }
  
  // 核心功能实现...
}

// 2. 依赖注入系统 - 服务加载

// 服务标识符
const IEditorService = createDecorator<IEditorService>('editorService');

// 服务接口
interface IEditorService {
  openEditor(input: IEditorInput, options?: IEditorOptions): Promise<IEditor | undefined>;
  // 更多API...
}

// 服务实现
@Injectable()
class EditorService implements IEditorService {
  constructor(
    @ICodeEditorService private readonly codeEditorService: ICodeEditorService,
    @IWorkbenchLayoutService private readonly layoutService: IWorkbenchLayoutService
  ) { }
  
  async openEditor(input: IEditorInput, options?: IEditorOptions): Promise<IEditor | undefined> {
    // 实现打开编辑器逻辑
  }
}

// 服务注册
class WorkbenchServiceRegistry {
  constructor() {
    // 注册核心服务
    registerSingleton(IEditorService, EditorService);
    registerSingleton(IWorkspaceService, WorkspaceService);
    registerSingleton(IFileService, FileService);
    // 更多服务注册...
  }
}

// 3. 扩展系统 - 主进程与扩展主机

// 扩展上下文
interface IExtensionContext {
  subscriptions: IDisposable[];
  extensionPath: string;
  storagePath?: string;
  // 更多属性...
}

// 扩展激活函数
function activate(context: IExtensionContext): API {
  // 扩展激活逻辑
  const disposable = registerCommand('extension.helloWorld', () => {
    window.showInformationMessage('Hello World!');
  });
  
  context.subscriptions.push(disposable);
  
  return {
    // 扩展API
  };
}

// 扩展主机环境
class ExtensionHostEnvironment {
  constructor(
    private readonly extensionService: IExtensionService,
    private readonly extensionHostWorker: Worker
  ) {
    // 初始化扩展环境
    this.setupMessageChannel();
  }
  
  private setupMessageChannel(): void {
    // 设置主进程和扩展进程间的通信
  }
  
  public async startExtensionHost(): Promise<void> {
    // 启动扩展主机
    await this.loadAndActivateExtensions();
  }
  
  private async loadAndActivateExtensions(): Promise<void> {
    // 加载并激活扩展
  }
}

// 4. 特性贡献点系统

interface ICommandContribution {
  readonly id: string;
  readonly handler: (...args: any[]) => any;
}

interface IViewContribution {
  readonly id: string;
  readonly name: string;
  readonly when?: ContextKeyExpression;
  createView(viewContainer: ViewContainer): IView;
}

class ContributionRegistry {
  private readonly _commands = new Map<string, ICommandContribution>();
  private readonly _views = new Map<string, IViewContribution>();
  
  registerCommand(contribution: ICommandContribution): IDisposable {
    this._commands.set(contribution.id, contribution);
    return {
      dispose: () => {
        this._commands.delete(contribution.id);
      }
    };
  }
  
  registerView(contribution: IViewContribution): IDisposable {
    this._views.set(contribution.id, contribution);
    return {
      dispose: () => {
        this._views.delete(contribution.id);
      }
    };
  }
  
  // 更多贡献点类型...
}

// 5. 工作台UI架构

class WorkbenchLayout {
  private readonly parts = new Map<WorkbenchPartId, Part>();
  
  constructor(
    @IInstantiationService private readonly instantiationService: IInstantiationService,
    @ILogService private readonly logService: ILogService
  ) {
    // 创建并注册工作台部件
    this.createParts();
  }
  
  private createParts(): void {
    // 创建各部件
    const activityBar = this.instantiationService.createInstance(ActivityBarPart);
    const sideBar = this.instantiationService.createInstance(SideBarPart);
    const editor = this.instantiationService.createInstance(EditorPart);
    const statusBar = this.instantiationService.createInstance(StatusBarPart);
    
    // 注册部件
    this.parts.set('activityBar', activityBar);
    this.parts.set('sideBar', sideBar);
    this.parts.set('editor', editor);
    this.parts.set('statusBar', statusBar);
  }
  
  layout(width: number, height: number): void {
    // 布局逻辑
  }
}

// 6. 语言服务协议集成

class LanguageClient {
  constructor(
    private readonly id: string,
    private readonly name: string,
    private readonly serverOptions: ServerOptions,
    private readonly clientOptions: LanguageClientOptions
  ) { }
  
  start(): Promise<void> {
    // 启动语言服务器
    return this.startServer().then(
      serverProcess => this.createConnection(serverProcess)
    ).then(
      connection => this.initialize(connection)
    );
  }
  
  private startServer(): Promise<ChildProcess | StreamInfo> {
    // 启动服务器进程
  }
  
  private createConnection(serverProcess: ChildProcess | StreamInfo): IConnection {
    // 建立与服务器的连接
  }
  
  private initialize(connection: IConnection): Promise<void> {
    // 初始化语言服务器
  }
}

// 7. Monaco编辑器集成

class MonacoEditorIntegration {
  constructor(
    @IModelService private readonly modelService: IModelService,
    @IConfigurationService private readonly configurationService: IConfigurationService
  ) { }
  
  createEditor(domElement: HTMLElement, options: IEditorConstructionOptions): ICodeEditor {
    // 创建Monaco编辑器实例
    const editor = monaco.editor.create(domElement, options);
    
    // 配置编辑器
    this.configureEditor(editor);
    
    return editor;
  }
  
  private configureEditor(editor: ICodeEditor): void {
    // 配置编辑器行为
  }
}
```

**VSCode架构特点**：

- 分层架构实现关注点分离
- 多进程架构提高稳定性与安全性
- 依赖注入支持松耦合和可测试性
- 扩展系统实现功能扩展
- 语言服务器协议支持丰富的语言功能
- Monaco编辑器提供核心编辑体验
- 事件驱动的响应式架构

### 6.2 Next.js内部架构

-**Next.js架构解析**

```javascript
// Next.js框架架构示例代码 - 简化概念性代码

// 1. 页面路由系统核心实现
// pages/_app.js (框架入口点)
import App from 'next/app';
import Head from 'next/head';
import Router from 'next/router';

// Next.js内部路由解析（概念性实现）
class RouterCore {
  constructor() {
    this.routes = new Map();
    this.dynamicRoutes = [];
    this.fallback = null;
  }
  
  // 解析路由配置
  addRoutes(pages) {
    // 添加静态路由
    for (const page of pages) {
      if (page.includes('[') && page.includes(']')) {
        // 处理动态路由: /posts/[id].js -> /posts/:id
        this.addDynamicRoute(page);
      } else {
        // 处理静态路由: /about.js -> /about
        this.addStaticRoute(page);
      }
    }
    
    // 添加API路由
    // ...
    
    // 添加中间件
    // ...
  }
  
  addStaticRoute(page) {
    const route = page.replace(/\.js$/, '').replace(/\/index$/, '/');
    this.routes.set(route, { page, dynamic: false });
  }
  
  addDynamicRoute(page) {
    // 转换 [id] 为 :id 格式
    const routePattern = page
      .replace(/\.js$/, '')
      .replace(/\/index$/, '/')
      .replace(/\[([^\]]+)\]/g, ':$1');
      
    // 创建路由匹配正则表达式
    const paramNames = [];
    const regexPattern = routePattern.replace(/:[^\/]+/g, (match) => {
      paramNames.push(match.slice(1));
      return '([^/]+)';
    });
    
    this.dynamicRoutes.push({
      page,
      pattern: new RegExp(`^${regexPattern}$`),
      paramNames
    });
  }
  
  // 路由匹配逻辑
  match(url) {
    // 1. 检查精确匹配
    if (this.routes.has(url)) {
      return {
        page: this.routes.get(url).page,
        params: {}
      };
    }
    
    // 2. 检查动态路由
    for (const route of this.dynamicRoutes) {
      const match = url.match(route.pattern);
      if (match) {
        const params = {};
        route.paramNames.forEach((name, i) => {
          params[name] = match[i + 1];
        });
        
        return {
          page: route.page,
          params
        };
      }
    }
    
    // 3. 回退到404或自定义404页面
    return {
      page: '/404',
      params: {}
    };
  }
}

// 2. 数据获取模型实现

// 客户端数据获取封装
function createClientDataFetcher() {
  const cache = new Map();
  
  return async function fetchData(key, fetchFn) {
    // 检查缓存
    if (cache.has(key)) {
      return cache.get(key);
    }
    
    // 获取数据
    try {
      const data = await fetchFn();
      cache.set(key, data);
      return data;
    } catch (error) {
      throw error;
    }
  };
}

// 服务端数据获取实现 - getStaticProps
async function executeGetStaticProps(page, params = {}) {
  // 加载页面模块
  const mod = await import(`../pages/${page}`);
  
  // 检查页面是否实现了getStaticProps
  if (typeof mod.getStaticProps !== 'function') {
    return { props: {} };
  }
  
  // 执行getStaticProps
  const context = { params };
  const result = await mod.getStaticProps(context);
  
  return result;
}

// 服务端数据获取实现 - getServerSideProps
async function executeGetServerSideProps(page, req, res, params = {}) {
  // 加载页面模块
  const mod = await import(`../pages/${page}`);
  
  // 检查页面是否实现了getServerSideProps
  if (typeof mod.getServerSideProps !== 'function') {
    return { props: {} };
  }
  
  // 执行getServerSideProps
  const context = { req, res, params };
  const result = await mod.getServerSideProps(context);
  
  return result;
}

// 3. 渲染引擎 - 服务端渲染实现

async function renderPageToHTML(page, req, res, params = {}) {
  // 加载页面组件
  const mod = await import(`../pages/${page}`);
  const Component = mod.default;
  
  // 获取数据
  let props = {};
  
  if (typeof mod.getServerSideProps === 'function') {
    // 使用getServerSideProps
    const result = await executeGetServerSideProps(page, req, res, params);
    props = result.props || {};
  } else if (typeof mod.getStaticProps === 'function') {
    // 使用getStaticProps
    const result = await executeGetStaticProps(page, params);
    props = result.props || {};
  }
  
  // 渲染页面
  const AppComponent = await import('../pages/_app').then(m => m.default);
  const html = ReactDOMServer.renderToString(
    <AppComponent Component={Component} pageProps={props} />
  );
  
  // 注入数据以便客户端hydration
  const dataScript = `
    <script id="__NEXT_DATA__" type="application/json">
      ${JSON.stringify({
        page,
        props,
        query: params,
        buildId: BUILD_ID
      })}
    </script>
  `;
  
  // 构造完整HTML
  return `
    <!DOCTYPE html>
    <html>
      <head>
        <!-- 头部内容 -->
      </head>
      <body>
        <div id="__next">${html}</div>
        ${dataScript}
        <!-- 客户端脚本 -->
      </body>
    </html>
  `;
}

// 4. 构建系统 - 多种渲染模式的处理

class NextBuildSystem {
  constructor(options) {
    this.options = options;
    this.pagesDir = options.pagesDir || './pages';
    this.outDir = options.outDir || './.next';
  }
  
  async build() {
    // 发现所有页面
    const pages = await this.discoverPages();
    
    // 分析每个页面的渲染模式
    const pageConfigs = await this.analyzePages(pages);
    
    // 生成客户端bundles
    await this.generateClientBundles(pageConfigs);
    
    // 根据渲染模式处理页面
    await this.processPages(pageConfigs);
    
    // 生成路由清单
    await this.generateRouteManifest(pageConfigs);
  }
  
  async analyzePages(pages) {
    const configs = [];
    
    for (const page of pages) {
      const mod = await import(page);
      
      let renderMode = 'SSR'; // 默认为服务端渲染
      
      if (mod.getStaticProps) {
        if (mod.getStaticPaths) {
          renderMode = 'SSG_DYNAMIC';
        } else {
          renderMode = 'SSG_STATIC';
        }
      } else if (mod.getServerSideProps) {
        renderMode = 'SSR';
      }
      
      configs.push({
        page,
        renderMode
      });
    }
    
    return configs;
  }
  
  async processPages(pageConfigs) {
    for (const config of pageConfigs) {
      switch (config.renderMode) {
        case 'SSG_STATIC':
          await this.handleStaticGeneration(config);
          break;
        case 'SSG_DYNAMIC':
          await this.handleDynamicStaticGeneration(config);
          break;
        case 'SSR':
          // SSR页面在运行时处理
          break;
      }
    }
  }
  
  async handleStaticGeneration(config) {
    // 执行getStaticProps
    const result = await executeGetStaticProps(config.page);
    
    // 渲染HTML
    const html = await this.renderPageToStatic(config.page, result.props);
    
    // 输出HTML文件
    const outputPath = this.getOutputPath(config.page);
    await fs.writeFile(outputPath, html);
  }
  
  async handleDynamicStaticGeneration(config) {
    // 获取所有可能的路径
    const mod = await import(config.page);
    const pathsResult = await mod.getStaticPaths();
    
    for (const params of pathsResult.paths) {
      // 为每个路径执行getStaticProps
      const result = await executeGetStaticProps(config.page, params);
      
      // 渲染HTML
      const html = await this.renderPageToStatic(config.page, result.props, params);
      
      // 确定输出路径
      const outputPath = this.getOutputPathWithParams(config.page, params);
      await fs.writeFile(outputPath, html);
    }
    
    // 处理fallback选项
    if (pathsResult.fallback) {
      // 生成fallback页面或配置
    }
  }
}

// 5. 中间件系统

class MiddlewareSystem {
  constructor() {
    this.middlewares = [];
  }
  
  use(middleware) {
    this.middlewares.push(middleware);
  }
  
  async run(req, res, next) {
    let index = 0;
    
    const executeMiddleware = async () => {
      if (index < this.middlewares.length) {
        const middleware = this.middlewares[index++];
        await middleware(req, res, executeMiddleware);
      } else {
        await next();
      }
    };
    
    await executeMiddleware();
  }
}

// 6. Incremental Static Regeneration实现

class ISRManager {
  constructor() {
    this.pages = new Map();
    this.revalidationQueue = new Set();
  }
  
  registerPage(path, { revalidate, lastGenerated = Date.now() }) {
    this.pages.set(path, {
      revalidate, // 重新验证间隔（秒）
      lastGenerated
    });
  }
  
  shouldRevalidate(path, timestamp = Date.now()) {
    const page = this.pages.get(path);
    if (!page) return false;
    
    const { revalidate, lastGenerated } = page;
    const timePassedSeconds = (timestamp - lastGenerated) / 1000;
    
    return timePassedSeconds >= revalidate;
  }
  
  async handleRequest(path, req, res) {
    // 尝试从缓存提供页面
    const cachedPage = await this.getCachedPage(path);
    
    // 检查是否需要后台重新验证
    if (this.shouldRevalidate(path)) {
      // 返回当前缓存版本
      res.send(cachedPage);
      
      // 后台触发重新生成
      this.triggerRegeneration(path, req);
    } else {
      // 直接返回缓存版本
      res.send(cachedPage);
    }
  }
  
  async triggerRegeneration(path, req) {
    // 防止重复重新生成
    if (this.revalidationQueue.has(path)) return;
    
    this.revalidationQueue.add(path);
    
    try {
      // 重新生成页面
      const newPage = await this.regeneratePage(path, req);
      
      // 更新缓存
      await this.updateCache(path, newPage);
      
      // 更新最后生成时间
      const page = this.pages.get(path);
      page.lastGenerated = Date.now();
      this.pages.set(path, page);
    } catch (error) {
      console.error(`Failed to regenerate page ${path}:`, error);
    } finally {
      this.revalidationQueue.delete(path);
    }
  }
}
```

**Next.js架构特点**：

- 基于文件系统的路由自动化
- 多种渲染模式统一集成
- 数据获取策略分离渲染与数据逻辑
- 增量静态再生成平衡静态与动态
- 内置中间件系统支持自定义逻辑
- 优化的构建系统针对生产环境
- 统一的APIs简化开发体验

### 6.3 Redis核心设计

-**Redis架构解析**

```c
// Redis架构示例代码 - 简化概念性代码

// 1. 核心数据结构

// 简化版的Redis对象系统
typedef struct redisObject {
    unsigned type:4;      // 对象类型：字符串、列表、哈希、集合、有序集合
    unsigned encoding:4;  // 对象编码：整数、embstr、raw、压缩字符串等
    unsigned lru:LRU_BITS;// 对象的LRU时间
    int refcount;         // 引用计数
    void *ptr;            //
指向实际数据结构的指针
} robj;

// 字符串 - 简单动态字符串(SDS)实现
struct sdshdr {
    int len;       // 已使用的字节数
    int free;      // 未使用的字节数
    char buf[];    // 柔性数组，实际存储数据
};

// 双端链表 - 用于列表对象
typedef struct listNode {
    struct listNode *prev; // 前置节点
    struct listNode *next; // 后置节点
    void *value;          // 节点值
} listNode;

typedef struct list {
    listNode *head;       // 链表头
    listNode *tail;       // 链表尾
    unsigned long len;    // 链表长度
    void *(*dup)(void *ptr); // 节点复制函数
    void (*free)(void *ptr); // 节点释放函数
    int (*match)(void *ptr, void *key); // 节点比较函数
} list;

// 字典 - 用于哈希对象，同时也是Redis数据库的底层实现
typedef struct dictEntry {
    void *key;                // 键
    union {
        void *val;
        uint64_t u64;
        int64_t s64;
        double d;
    } v;                      // 值可以是多种类型
    struct dictEntry *next;   // 下一个哈希表节点（链地址法解决冲突）
} dictEntry;

typedef struct dictht {
    dictEntry **table;        // 哈希表数组
    unsigned long size;       // 哈希表大小
    unsigned long sizemask;   // 哈希表大小掩码，用于计算索引值
    unsigned long used;       // 已有节点数量
} dictht;

typedef struct dict {
    dictType *type;           // 类型特定函数
    void *privdata;           // 私有数据
    dictht ht[2];             // 两个哈希表，用于渐进式rehash
    long rehashidx;           // rehash索引，-1表示没有进行rehash
    int iterators;            // 当前正在使用的迭代器数量
} dict;

// 跳表 - 用于有序集合对象
typedef struct zskiplistNode {
    sds ele;                  // 元素
    double score;             // 分值
    struct zskiplistNode *backward; // 后退指针
    struct zskiplistLevel {
        struct zskiplistNode *forward; // 前进指针
        unsigned int span;    // 跨度
    } level[];               // 层
} zskiplistNode;

typedef struct zskiplist {
    struct zskiplistNode *header, *tail; // 头尾节点
    unsigned long length;     // 节点数量
    int level;                // 当前最大层数
} zskiplist;

// 整数集合 - 用于小整数集合
typedef struct intset {
    uint32_t encoding;        // 编码方式 
    uint32_t length;          // 集合包含的元素数量
    int8_t contents[];        // 实际存储的元素，可能是int16_t/int32_t/int64_t
} intset;

// 2. 事件循环系统

// 文件事件结构
typedef struct aeFileEvent {
    int mask;                 // 事件类型掩码 AE_READABLE | AE_WRITABLE
    aeFileProc *rfileProc;    // 读事件处理器
    aeFileProc *wfileProc;    // 写事件处理器
    void *clientData;         // 客户端私有数据
} aeFileEvent;

// 时间事件结构
typedef struct aeTimeEvent {
    long long id;             // 时间事件ID
    long when_sec;            // 秒
    long when_ms;             // 毫秒
    aeTimeProc *timeProc;     // 时间事件处理器
    aeEventFinalizerProc *finalizerProc; // 事件释放处理器
    void *clientData;         // 客户端私有数据
    struct aeTimeEvent *next; // 指向下个节点的指针
} aeTimeEvent;

// 事件循环
typedef struct aeEventLoop {
    int maxfd;                // 当前注册的最大文件描述符
    int setsize;              // 事件池大小
    long long timeEventNextId; // 下一个时间事件ID
    time_t lastTime;          // 上一次执行时间事件的时间
    aeFileEvent *events;      // 已注册的文件事件
    aeFiredEvent *fired;      // 已触发的文件事件
    aeTimeEvent *timeEventHead; // 时间事件链表头
    int stop;                  // 停止标志
    void *apidata;             // 底层多路复用库的私有数据
    aeBeforeSleepProc *beforesleep; // 处理事件前要执行的函数
    aeBeforeSleepProc *aftersleep;  // 处理事件后要执行的函数
} aeEventLoop;

// 事件循环主函数
void aeMain(aeEventLoop *eventLoop) {
    eventLoop->stop = 0;
    while (!eventLoop->stop) {
        // 如果有需要在处理事件前执行的函数，那么执行它
        if (eventLoop->beforesleep != NULL)
            eventLoop->beforesleep(eventLoop);
            
        // 开始处理事件
        aeProcessEvents(eventLoop, AE_ALL_EVENTS | AE_CALL_AFTER_SLEEP);
    }
}

// 事件处理
int aeProcessEvents(aeEventLoop *eventLoop, int flags) {
    int processed = 0;
    
    // 获取最近的时间事件
    tvp = ...
    
    // 调用多路复用API阻塞等待事件发生
    numevents = aeApiPoll(eventLoop, tvp);
    
    // 处理文件事件
    for (j = 0; j < numevents; j++) {
        // 获取被触发的事件
        aeFileEvent *fe = &eventLoop->events[eventLoop->fired[j].fd];
        int mask = eventLoop->fired[j].mask;
        int fd = eventLoop->fired[j].fd;
        
        // 如果是读事件，调用读事件处理器
        if (fe->mask & mask & AE_READABLE) {
            fe->rfileProc(eventLoop, fd, fe->clientData, mask);
        }
        
        // 如果是写事件，调用写事件处理器
        if (fe->mask & mask & AE_WRITABLE) {
            fe->wfileProc(eventLoop, fd, fe->clientData, mask);
        }
        
        processed++;
    }
    
    // 处理时间事件
    if (flags & AE_TIME_EVENTS)
        processed += processTimeEvents(eventLoop);
        
    return processed;
}

// 3. 持久化机制

// RDB持久化
int rdbSave(char *filename) {
    // 创建临时文件
    snprintf(tmpfile, 256, "temp-%d.rdb", (int) getpid());
    fp = fopen(tmpfile, "w");
    
    // 初始化保存操作的状态
    rio rdb;
    rioInitWithFile(&rdb, fp);
    
    // 写入RDB文件头部
    if (rdbWriteRaw(&rdb, "REDIS", 5) == -1) goto error;
    
    // 写入版本号
    if (rdbSaveRio(&rdb, RDBFLAGS_NONE, &error) == -1) goto error;
    
    // 关闭文件并进行原子替换
    fclose(fp);
    return rename(tmpfile, filename);
    
error:
    // 错误处理
    fclose(fp);
    unlink(tmpfile);
    return -1;
}

// AOF持久化

// 追加AOF命令
void feedAppendOnlyFile(struct redisCommand *cmd, int dictid, robj **argv, int argc) {
    sds buf = sdsempty();
    
    // 添加多数据库选择命令
    if (dictid != server.aof_selected_db) {
        buf = sdscatprintf(buf, "*2\r\n$6\r\nSELECT\r\n$%d\r\n%d\r\n",
            intlen(dictid), dictid);
        server.aof_selected_db = dictid;
    }
    
    // 将命令转换为RESP格式
    buf = catAppendOnlyGenericCommand(buf, argc, argv);
    
    // 将命令追加到AOF缓冲区
    if (server.aof_state == AOF_ON)
        server.aof_buf = sdscatlen(server.aof_buf, buf, sdslen(buf));
    
    // 将命令传入所有从节点
    if (server.replication_mode == REPLICATION_MODE_MASTER)
        replicationFeedSlaves(server.slaves, cmd, dictid, argv, argc);
    
    sdsfree(buf);
}

// AOF重写
int rewriteAppendOnlyFile(char *filename) {
    // 创建临时文件
    snprintf(tmpfile, 256, "temp-rewriteaof-%d.aof", (int) getpid());
    fp = fopen(tmpfile, "w");
    
    // 初始化写入状态
    rio aof;
    rioInitWithFile(&aof, fp);
    
    // 遍历所有数据库，生成重建命令
    for (j = 0; j < server.dbnum; j++) {
        // 选择数据库
        if (dictSize(db->dict) == 0) continue;
        
        // 生成SELECT命令
        buf = sdscatprintf(sdsempty(), "*2\r\n$6\r\nSELECT\r\n$%d\r\n%d\r\n",
                           len, j);
        if (rioWrite(&aof, buf, sdslen(buf)) == 0) goto werr;
        
        // 遍历当前数据库的所有键
        de = dictGetIterator(db->dict);
        while((de = dictNext(de)) != NULL) {
            // 根据键的类型生成不同的重建命令
            if (key->type == REDIS_STRING) {
                // 处理字符串
            } else if (key->type == REDIS_LIST) {
                // 处理列表
            } else if (key->type == REDIS_SET) {
                // 处理集合
            } else if (key->type == REDIS_ZSET) {
                // 处理有序集合
            } else if (key->type == REDIS_HASH) {
                // 处理哈希表
            }
        }
    }
    
    // 关闭文件并进行原子替换
    fclose(fp);
    return rename(tmpfile, filename);
    
werr:
    // 错误处理
    fclose(fp);
    unlink(tmpfile);
    return -1;
}

// 4. 主从复制机制

// 复制状态
typedef struct replstate {
    int masterfd;            // 连接到主服务器的套接字
    long long master_repl_offset; // 复制偏移量
    char *masterhost;        // 主服务器的地址
    int masterport;          // 主服务器的端口
    int repl_state;          // 复制状态
    // ... 更多复制状态
} replstate;

// 将服务器设置为某个服务器的从服务器
void replicationSetMaster(char *ip, int port) {
    int was_master = server.masterhost == NULL;
    
    // 设置主服务器
    sdsfree(server.masterhost);
    server.masterhost = sdsnew(ip);
    server.masterport = port;
    
    // 如果之前是主服务器，且执行复制的是自己，那么尝试传播新配置
    if (was_master && server.repl_state == REPL_STATE_CONNECTED)
        replicationUnsetMaster();
    
    // 初始化复制为REPL_STATE_CONNECT
    server.repl_state = REPL_STATE_CONNECT;
}

// 与主服务器同步
void syncWithMaster(aeEventLoop *el, int fd, void *privdata, int mask) {
    char buf[1024], tmpfile[256];
    int dfd, maxtries = 5;
    
    // 如果当前不是REPL_STATE_CONNECTING，返回
    if (server.repl_state != REPL_STATE_CONNECTING) return;
    
    // 尝试读取 +OK 响应
    if (syncReadLine(fd, buf, sizeof(buf), server.repl_syncio_timeout) == -1) {
        replicationSetState(REPL_STATE_CONNECT);
        return;
    }
    
    // 如果接收到的不是 +OK，尝试重新连接
    if (buf[0] != '+' || buf[1] != 'O' || buf[2] != 'K') {
        replicationSetState(REPL_STATE_CONNECT);
        return;
    }
    
    // 发送端口信息
    if (snprintf(...) && syncWrite(...)) {
        replicationSetState(REPL_STATE_CONNECT);
        return;
    }
    
    // 读取缓冲区的数据
    while(maxtries--) {
        int nread = read(fd, buf, sizeof(buf));
        
        if (nread <= 0) {
            replicationSetState(REPL_STATE_CONNECT);
            return;
        }
        
        // 处理读取到的数据
    }
    
    // 设置状态为已连接
    replicationSetState(REPL_STATE_CONNECTED);
}

// 向所有从服务器发送数据
void replicationFeedSlaves(list *slaves, struct redisCommand *cmd, int dictid, robj **argv, int argc) {
    listNode *ln;
    listIter li;
    
    // 快速返回：如果没有从服务器，直接返回
    if (listLength(slaves) == 0) return;
    
    // 向所有从服务器发送命令
    listRewind(slaves, &li);
    while((ln = listNext(&li))) {
        redisClient *slave = ln->value;
        
        // 检查从服务器状态
        if (slave->replstate != REDIS_REPL_ONLINE) continue;
        
        // 将命令添加到从服务器的输出缓冲区
        addReply(slave, cmd);
        
        // 更新复制偏移量
        slave->repldboff += size;
    }
}

// 5. 集群模式

// 集群节点结构
typedef struct clusterNode {
    mstime_t ctime;           // 创建节点的时间
    char name[REDIS_CLUSTER_NAMELEN]; // 节点名称
    int flags;                // 节点标志，例如主节点、从节点、下线等
    uint64_t configEpoch;     // 节点配置版本
    unsigned char slots[REDIS_CLUSTER_SLOTS/8]; // 槽位图
    int numslots;             // 负责处理的槽位数量
    int numslaves;            // 从节点数量
    struct clusterNode **slaves; // 从节点数组
    struct clusterNode *slaveof; // 如果是从节点，指向主节点
    mstime_t ping_sent;       // 最后一次发送ping的时间
    mstime_t pong_received;   // 最后一次接收pong的时间
    mstime_t fail_time;       // 被标记为FAIL的时间
    mstime_t voted_time;      // 投票时间
    mstime_t repl_offset_time; // 最后一次更新复制偏移量的时间
    long long repl_offset;    // 复制偏移量
    char ip[REDIS_IP_STR_LEN]; // 节点的IP地址
    int port;                 // 节点的端口
    int cport;                // 节点的集群端口
    clusterLink *link;        // TCP链接
    list *fail_reports;       // 节点下线报告
} clusterNode;

// 集群结构
typedef struct clusterState {
    clusterNode *myself;       // 指向当前节点的指针
    uint64_t currentEpoch;     // 当前配置纪元
    int state;                 // 集群状态
    int size;                  // 集群中的节点数量
    dict *nodes;               // 集群节点名称与节点指针的映射
    dict *nodes_black_list;    // 节点黑名单
    clusterNode *migrating_slots_to[REDIS_CLUSTER_SLOTS]; // 迁移槽的目标节点
    clusterNode *importing_slots_from[REDIS_CLUSTER_SLOTS]; // 导入槽的源节点
    clusterNode *slots[REDIS_CLUSTER_SLOTS]; // 处理每个槽的节点
    uint64_t slots_keys_count[REDIS_CLUSTER_SLOTS]; // 槽中键的数量
    rax *slots_to_keys;        // 槽到键的映射
} clusterState;

// 键到槽的映射
unsigned int keyHashSlot(char *key, int keylen) {
    int s, e; // 开始和结束位置
    
    // 查找 {
    for (s = 0; s < keylen; s++)
        if (key[s] == '{') break;
    
    // 未找到 {，使用全部key进行计算
    if (s == keylen) return crc16(key, keylen) & 16383;
    
    // 查找 }
    for (e = s+1; e < keylen; e++)
        if (key[e] == '}') break;
    
    // 未找到 }，使用全部key进行计算
    if (e == keylen || e == s+1) return crc16(key, keylen) & 16383;
    
    // 使用 {} 之间的子串进行计算
    return crc16(key+s+1, e-s-1) & 16383;
}

// 发送集群消息
void clusterSendMessage(clusterLink *link, unsigned char *msg, size_t msglen) {
    if (link->node && link->node->flags & REDIS_NODE_PING_SENT)
        link->node->ping_sent = 0;
    
    // 将消息写入输出缓冲区
    if (sdslen(link->sndbuf) == 0 && msglen != 0)
        aeCreateFileEvent(server.el, link->fd, AE_WRITABLE, clusterWriteHandler, link);
    
    link->sndbuf = sdscatlen(link->sndbuf, msg, msglen);
}

// 处理集群消息
void clusterProcessPacket(clusterLink *link) {
    clusterMsg *hdr = (clusterMsg*) link->rcvbuf;
    uint32_t totlen = ntohl(hdr->totlen);
    uint16_t type = ntohs(hdr->type);
    
    // 如果消息长度不够，等待更多数据
    if (totlen < 8) return;
    if (totlen > sdslen(link->rcvbuf)) return;
    
    // 根据消息类型处理不同的消息
    if (type == CLUSTERMSG_TYPE_PING) {
        // 处理PING消息
        clusterProcessPingMessage(link, hdr);
    } else if (type == CLUSTERMSG_TYPE_PONG) {
        // 处理PONG消息
        clusterProcessPongMessage(link, hdr);
    } else if (type == CLUSTERMSG_TYPE_MEET) {
        // 处理MEET消息
        clusterProcessMeetMessage(link, hdr);
    } else if (type == CLUSTERMSG_TYPE_FAIL) {
        // 处理FAIL消息
        clusterProcessFailMessage(link, hdr);
    } else if (type == CLUSTERMSG_TYPE_PUBLISH) {
        // 处理PUBLISH消息
        clusterProcessPublishMessage(link, hdr);
    } else if (type == CLUSTERMSG_TYPE_UPDATE) {
        // 处理UPDATE消息
        clusterProcessUpdateMessage(link, hdr);
    }
    
    // 移除已处理的消息
    sdsrange(link->rcvbuf, totlen, -1);
}

// 6. 内存优化

// 对象共享
void createSharedObjects(void) {
    int j;
    
    // 创建共享字符串对象
    shared.crlf = createObject(REDIS_STRING, sdsnew("\r\n"));
    shared.ok = createObject(REDIS_STRING, sdsnew("+OK\r\n"));
    shared.err = createObject(REDIS_STRING, sdsnew("-ERR\r\n"));
    
    // 创建共享整数对象
    for (j = 0; j < REDIS_SHARED_INTEGERS; j++) {
        shared.integers[j] = createObject(REDIS_STRING, (void*)(long)j);
        shared.integers[j]->encoding = REDIS_ENCODING_INT;
    }
    
    // 创建其他共享对象
    shared.nullbulk = createObject(REDIS_STRING, sdsnew("$-1\r\n"));
    shared.nullmultibulk = createObject(REDIS_STRING, sdsnew("*-1\r\n"));
    shared.emptymultibulk = createObject(REDIS_STRING, sdsnew("*0\r\n"));
}

// 内存回收策略 - 基于LRU的对象驱逐
robj *lookupKey(redisDb *db, robj *key, int flags) {
    dictEntry *de = dictFind(db->dict, key->ptr);
    if (de) {
        robj *val = dictGetVal(de);
        
        // 根据需要，更新对象的LRU时间
        if (!(flags & REDIS_LOOKUP_NOTOUCH)) {
            if (server.maxmemory_policy & REDIS_MAXMEMORY_FLAG_LRU)
                val->lru = getLRUClock();
        }
        return val;
    } else {
        return NULL;
    }
}

// 内存淘汰算法
int freeMemoryIfNeeded(void) {
    // 如果没有设置最大内存限制，直接返回
    if (!server.maxmemory) return REDIS_OK;
    
    // 超过限制的内存量
    size_t mem_used = zmalloc_used_memory();
    if (mem_used <= server.maxmemory) return REDIS_OK;
    
    mem_tofree = mem_used - server.maxmemory;
    
    // 根据淘汰策略选择要驱逐的键
    switch(server.maxmemory_policy) {
        case REDIS_MAXMEMORY_VOLATILE_LRU:
            // 在设置了过期时间的键中选择最久未使用的键
            return freeMemoryUsingLRU(mem_tofree, 1);
        case REDIS_MAXMEMORY_ALLKEYS_LRU:
            // 在所有键中选择最久未使用的键
            return freeMemoryUsingLRU(mem_tofree, 0);
        case REDIS_MAXMEMORY_VOLATILE_RANDOM:
            // 在设置了过期时间的键中随机选择
            return freeMemoryUsingRandom(mem_tofree, 1);
        case REDIS_MAXMEMORY_ALLKEYS_RANDOM:
            // 在所有键中随机选择
            return freeMemoryUsingRandom(mem_tofree, 0);
        case REDIS_MAXMEMORY_VOLATILE_TTL:
            // 在设置了过期时间的键中选择即将过期的键
            return freeMemoryUsingTTL(mem_tofree);
        case REDIS_MAXMEMORY_NO_EVICTION:
            // 不驱逐键，返回错误
            return REDIS_ERR;
        default:
            // 未知策略，应该不会发生
            return REDIS_ERR;
    }
}
```

**Redis架构特点**：

- 多样化的内存数据结构
- 单线程事件循环模型
- 持久化机制保证数据安全
- 主从复制实现数据分发
- 集群模式支持水平扩展
- 内存优化实现高效运行
- 扩展命令通过模块系统实现

### 6.4 Kubernetes架构原理

-**Kubernetes架构解析**

```go
// Kubernetes架构示例代码 - 简化概念性代码

// 1. API服务器 - 核心组件

// 主要结构体
type APIServer struct {
    GenericAPIServer *genericapiserver.GenericAPIServer
    Authenticator    authenticator.Request
    Authorizer       authorizer.Authorizer
    AdmissionControl admission.Interface
    MasterCount      int
    // 其他字段...
}

// 安装API组
func (s *APIServer) InstallAPIs(apiResourceConfigSource serverstorage.APIResourceConfigSource,
    restOptionsGetter generic.RESTOptionsGetter,
    groupInfos []apiservicerest.StorageGroupInfo) {
    
    // 安装核心API
    legacyRESTStorageProvider := corerest.LegacyRESTStorageProvider{
        StorageFactory:        s.StorageFactory,
        ProxyTransport:        s.ProxyTransport,
        KubeletClientConfig:   s.KubeletClientConfig,
        EventTTL:              s.EventTTL,
        ServiceIPRange:        s.ServiceIPRange,
        SecondaryServiceIPRange: s.SecondaryServiceIPRange,
        ServiceNodePortRange:  s.ServiceNodePortRange,
        LoopbackClientConfig:  s.LoopbackClientConfig,
    }
    
    apiGroupInfo, err := legacyRESTStorageProvider.NewLegacyRESTStorage(restOptionsGetter)
    if err != nil {
        log.Fatal(err)
    }
    
    if err := s.GenericAPIServer.InstallLegacyAPIGroup("/api", &apiGroupInfo); err != nil {
        log.Fatal(err)
    }
    
    // 安装扩展API
    for _, groupInfo := range groupInfos {
        if err := s.GenericAPIServer.InstallAPIGroup(&groupInfo); err != nil {
            log.Fatal(err)
        }
    }
}

// 2. Etcd存储 - 所有Kubernetes对象的持久化存储

// 存储接口
type Storage interface {
    // 创建对象
    Create(ctx context.Context, key string, obj, out runtime.Object, ttl uint64) error
    
    // 删除对象
    Delete(ctx context.Context, key string, out runtime.Object, preconditions *Preconditions) error
    
    // 获取对象
    Get(ctx context.Context, key string, opts GetOptions, objPtr runtime.Object) error
    
    // 获取列表
    GetList(ctx context.Context, key string, opts ListOptions, listObj runtime.Object) error
    
    // 监视对象变化
    Watch(ctx context.Context, key string, opts ListOptions) (watch.Interface, error)
    
    // 更新对象
    GuaranteedUpdate(
        ctx context.Context, key string, ptrToType runtime.Object, ignoreNotFound bool,
        preconditions *Preconditions, tryUpdate UpdateFunc, suggestion ...runtime.Object) error
}

// Etcd3存储实现
type etcd3Storage struct {
    client *clientv3.Client
    codec  runtime.Codec
    prefix string
    // 其他字段...
}

// 实现Create方法
func (s *etcd3Storage) Create(ctx context.Context, key string, obj, out runtime.Object, ttl uint64) error {
    // 序列化对象
    data, err := runtime.Encode(s.codec, obj)
    if err != nil {
        return err
    }
    
    // 创建事务
    txn := s.client.Txn(ctx)
    
    // 构建创建操作，确保key不存在
    txn = txn.If(clientv3.Compare(clientv3.ModRevision(key), "=", 0))
    
    // 设置TTL如果需要
    var opts []clientv3.OpOption
    if ttl > 0 {
        lease, err := s.client.Grant(ctx, int64(ttl))
        if err != nil {
            return err
        }
        opts = append(opts, clientv3.WithLease(lease.ID))
    }
    
    // 如果key不存在，则创建它
    txn = txn.Then(clientv3.OpPut(key, string(data), opts...))
    
    // 执行事务
    txnRe
sp, err := txn.Commit()
    if err != nil {
        return err
    }
    
    // 检查事务是否成功
    if !txnResp.Succeeded {
        return storage.NewKeyExistsError(key, 0)
    }
    
    // 将创建的对象解码到输出参数
    if out != nil {
        return decode(s.codec, s.versioner, data, out, txnResp.Header.Revision)
    }
    
    return nil
}

// 3. Controller Manager - 控制器的管理者

// 控制器管理器结构
type ControllerManager struct {
    // 配置信息
    componentConfig      ControllerManagerConfiguration
    
    // 客户端配置
    kubeClient           clientset.Interface
    
    // 控制器上下文
    ControllerContext    ControllerContext
    
    // 是否运行领导者选举
    leaderElection       bool
    
    // 活跃控制器映射
    activeControllers    map[string]bool
    
    // 其他字段...
}

// 运行所有控制器
func (cm *ControllerManager) Run(ctx context.Context) error {
    // 启动健康检查服务
    go cm.startHealthzServer()
    
    // 如果需要，运行领导者选举
    if cm.leaderElection {
        go cm.runLeaderElection(ctx)
    } else {
        // 直接启动所有控制器
        cm.startControllers(ctx)
    }
    
    <-ctx.Done()
    return nil
}

// 启动各个控制器
func (cm *ControllerManager) startControllers(ctx context.Context) {
    controllers := map[string]initFunc{
        "endpoint":        startEndpointController,
        "replication":     startReplicationController,
        "podgc":           startPodGCController,
        "deployment":      startDeploymentController,
        "job":             startJobController,
        "statefulset":     startStatefulSetController,
        "cronjob":         startCronJobController,
        "namespace":       startNamespaceController,
        "serviceaccount":  startServiceAccountController,
        "garbagecollector": startGarbageCollectorController,
        // 更多控制器...
    }
    
    // 启动指定的控制器
    for controllerName, initFn := range controllers {
        if !cm.IsControllerEnabled(controllerName) {
            continue
        }
        
        // 标记控制器为活跃
        cm.activeControllers[controllerName] = true
        
        // 启动控制器
        go func(name string, fn initFunc) {
            defer utilruntime.HandleCrash()
            
            // 初始化并启动控制器
            if err := fn(cm.ControllerContext); err != nil {
                log.Errorf("Error starting %s controller: %v", name, err)
            }
        }(controllerName, initFn)
    }
}

// 领导者选举
func (cm *ControllerManager) runLeaderElection(ctx context.Context) {
    // 创建领导者选举对象
    leaderElectionClient := clientset.NewForConfigOrDie(cm.leaderElectionClient)
    resourceLock, err := resourcelock.New(
        cm.componentConfig.Generic.LeaderElection.ResourceLock,
        cm.componentConfig.Generic.LeaderElection.ResourceNamespace,
        cm.componentConfig.Generic.LeaderElection.ResourceName,
        leaderElectionClient.CoreV1(),
        leaderElectionClient.CoordinationV1(),
        resourcelock.ResourceLockConfig{
            Identity:      cm.componentConfig.Generic.LeaderElection.ResourceName,
            EventRecorder: cm.eventRecorder,
        },
    )
    if err != nil {
        log.Fatalf("error creating lock: %v", err)
    }
    
    // 开始领导者选举
    leaderelection.RunOrDie(ctx, leaderelection.LeaderElectionConfig{
        Lock:          resourceLock,
        LeaseDuration: cm.componentConfig.Generic.LeaderElection.LeaseDuration.Duration,
        RenewDeadline: cm.componentConfig.Generic.LeaderElection.RenewDeadline.Duration,
        RetryPeriod:   cm.componentConfig.Generic.LeaderElection.RetryPeriod.Duration,
        Callbacks: leaderelection.LeaderCallbacks{
            OnStartedLeading: func(ctx context.Context) {
                // 成为领导者后启动所有控制器
                cm.startControllers(ctx)
            },
            OnStoppedLeading: func() {
                // 失去领导者身份后退出
                log.Fatalf("leaderelection lost")
            },
        },
    })
}

// 4. Deployment控制器 - 作为具体控制器的示例

// Deployment控制器结构
type DeploymentController struct {
    // 客户端
    client clientset.Interface
    
    // 事件记录器
    eventRecorder record.EventRecorder
    
    // Deployment信息队列
    queue workqueue.RateLimitingInterface
    
    // 各种Informer
    dLister       appslisters.DeploymentLister
    dListerSynced cache.InformerSynced
    rsLister      appslisters.ReplicaSetLister
    rsListerSynced cache.InformerSynced
    podLister     corelisters.PodLister
    podListerSynced cache.InformerSynced
}

// 启动Deployment控制器
func startDeploymentController(ctx context.Context, controllerContext ControllerContext) error {
    dc, err := NewDeploymentController(
        controllerContext.ClientBuilder.ClientOrDie("deployment-controller"),
        controllerContext.InformerFactory.Apps().V1().Deployments(),
        controllerContext.InformerFactory.Apps().V1().ReplicaSets(),
        controllerContext.InformerFactory.Core().V1().Pods(),
    )
    if err != nil {
        return err
    }
    
    // 启动控制器
    go dc.Run(ctx, int(controllerContext.ComponentConfig.DeploymentController.ConcurrentDeploymentSyncs))
    return nil
}

// 控制器主循环
func (dc *DeploymentController) Run(ctx context.Context, workers int) {
    defer utilruntime.HandleCrash()
    defer dc.queue.ShutDown()
    
    log.Info("Starting deployment controller")
    defer log.Info("Shutting down deployment controller")
    
    // 等待缓存同步
    if !cache.WaitForNamedCacheSync("deployment-controller", ctx.Done(),
        dc.dListerSynced, dc.rsListerSynced, dc.podListerSynced) {
        return
    }
    
    // 启动worker
    for i := 0; i < workers; i++ {
        go wait.UntilWithContext(ctx, dc.worker, time.Second)
    }
    
    <-ctx.Done()
}

// Worker处理队列中的Deployment
func (dc *DeploymentController) worker(ctx context.Context) {
    for dc.processNextWorkItem(ctx) {
    }
}

// 处理单个工作项
func (dc *DeploymentController) processNextWorkItem(ctx context.Context) bool {
    // 从队列获取下一个项目
    key, quit := dc.queue.Get()
    if quit {
        return false
    }
    defer dc.queue.Done(key)
    
    // 处理项目
    err := dc.syncHandler(ctx, key.(string))
    if err != nil {
        // 处理错误，可能重试
        dc.queue.AddRateLimited(key)
        return true
    }
    
    // 处理成功，移除限速
    dc.queue.Forget(key)
    return true
}

// 同步Deployment
func (dc *DeploymentController) syncHandler(ctx context.Context, key string) error {
    startTime := time.Now()
    defer func() {
        log.V(4).Infof("Finished syncing deployment %q (%v)", key, time.Since(startTime))
    }()
    
    // 解析命名空间和名称
    namespace, name, err := cache.SplitMetaNamespaceKey(key)
    if err != nil {
        return err
    }
    
    // 获取Deployment
    deployment, err := dc.dLister.Deployments(namespace).Get(name)
    if errors.IsNotFound(err) {
        log.V(2).Infof("Deployment %v has been deleted", key)
        return nil
    }
    if err != nil {
        return err
    }
    
    // 深拷贝避免修改缓存
    d := deployment.DeepCopy()
    
    // 实现Deployment逻辑
    return dc.syncDeployment(ctx, d)
}

// 5. Kubelet - 节点代理

// Kubelet结构
type Kubelet struct {
    // 主机名
    hostname string
    
    // 节点名称
    nodeName string
    
    // 运行时
    containerRuntime container.Runtime
    
    // Pod管理器
    podManager podmanager.Manager
    
    // 卷管理器
    volumeManager volume.Manager
    
    // 状态管理器
    statusManager status.Manager
    
    // 探针管理器
    probeManager prober.Manager
    
    // 容器垃圾回收器
    containerGC kubecontainer.ContainerGC
    
    // 镜像垃圾回收器
    imageManager images.ImageGCManager
    
    // 网络插件
    networkPlugin network.NetworkPlugin
    
    // 其他字段...
}

// 运行Kubelet
func (kl *Kubelet) Run(updates <-chan kubetypes.PodUpdate) {
    // 启动Kubelet服务
    if err := kl.initializeModules(); err != nil {
        log.Errorf("Failed to initialize kubelet modules: %v", err)
        os.Exit(1)
    }
    
    // 注册节点
    go kl.registerNode()
    
    // 启动状态同步循环
    go wait.Until(kl.syncNodeStatus, kl.nodeStatusUpdateFrequency, wait.NeverStop)
    
    // 启动容器垃圾回收循环
    go wait.Until(kl.containerGC.GarbageCollect, ContainerGCPeriod, wait.NeverStop)
    
    // 启动镜像垃圾回收循环
    go wait.Until(kl.imageManager.GarbageCollect, ImageGCPeriod, wait.NeverStop)
    
    // 启动卷管理器
    go kl.volumeManager.Run(kl.sourcesReady, wait.NeverStop)
    
    // 启动Pod处理循环
    kl.syncLoop(updates, kl)
}

// Pod同步循环
func (kl *Kubelet) syncLoop(updates <-chan kubetypes.PodUpdate, handler SyncHandler) {
    // 事件类型到处理函数的映射
    eventHandlers := map[kubetypes.PodEventType]func(*v1.Pod){
        kubetypes.ADD:    handler.HandlePodAdditions,
        kubetypes.UPDATE: handler.HandlePodUpdates,
        kubetypes.REMOVE: handler.HandlePodRemoves,
        kubetypes.RECONCILE: handler.HandlePodReconcile,
    }
    
    for {
        select {
        case u := <-updates:
            // 处理Pod更新
            kl.handlePodUpdates(u)
            
            // 调用相应的事件处理函数
            if handler, ok := eventHandlers[u.Op]; ok {
                for _, pod := range u.Pods {
                    handler(pod)
                }
            }
        case <-kl.syncCh:
            // 定期同步
            kl.HandlePodSyncs(kl.podManager.GetPods())
        case <-kl.houseKeepingCh:
            // 内务处理
            kl.HandlePodCleanups()
        }
    }
}

// 处理Pod添加
func (kl *Kubelet) HandlePodAdditions(pods []*v1.Pod) {
    // 对Pod进行排序，优先启动高优先级的Pod
    sort.Sort(kubetypes.ByCreationTimestamp(pods))
    
    for _, pod := range pods {
        // 添加Pod到管理器
        kl.podManager.AddPod(pod)
        
        // 记录Pod添加事件
        kl.recordPodEvent(pod, v1.EventTypeNormal, events.PodScheduled, "Pod scheduled to node")
        
        // 创建Pod目录
        if err := kl.makePodDataDir(pod); err != nil {
            log.Errorf("Unable to make pod data directories for pod %q: %v", pod.Name, err)
            continue
        }
        
        // 启动Pod
        kl.dispatchWork(pod, kubetypes.SyncPodCreate, nil, waitGroup)
        
        // 更新Pod状态
        kl.statusManager.SetPodStatus(pod, v1.PodStatus{Phase: v1.PodPending})
    }
}

// 执行Pod同步
func (kl *Kubelet) syncPod(ctx context.Context, updateType kubetypes.SyncPodType, pod *v1.Pod, mirrorPod *v1.Pod, podStatus *kubecontainer.PodStatus) (isTerminal bool, err error) {
    // 检查Pod是否允许运行在当前节点
    if !kl.canRunPod(pod) {
        return false, fmt.Errorf("Pod %s is not allowed to run on node %s", pod.Name, kl.nodeName)
    }
    
    // 准备工作
    // 1. 创建Pod目录和卷目录
    // 2. 挂载Secrets和ConfigMaps
    // 3. 配置网络
    
    // 运行时启动Pod
    result := kl.containerRuntime.SyncPod(pod, podStatus, kl.backOff)
    
    // 处理结果
    // 1. 处理容器启动错误
    // 2. 更新Pod状态
    // 3. 处理可能的Pod终止
    
    return result.IsTerminal(), nil
}

// 6. Kube-Proxy - 网络代理

// Kube-Proxy结构
type ProxyServer struct {
    // Proxier接口实现
    Proxier proxy.Provider
    
    // 客户端
    Client clientset.Interface
    
    // 事件记录器
    Recorder record.EventRecorder
    
    // 工作队列
    serviceChanges proxy.ServiceChangeTracker
    endpointsChanges proxy.EndpointsChangeTracker
    
    // 其他字段...
}

// 启动ProxyServer
func (s *ProxyServer) Run() error {
    // 初始化
    if err := s.initialize(); err != nil {
        return err
    }
    
    // 启动信息器
    informerFactory := informers.NewSharedInformerFactory(s.Client, s.ConfigSyncPeriod)
    
    // 配置服务处理器
    serviceConfig := config.NewServiceConfig(
        informerFactory.Core().V1().Services(),
        s.ConfigSyncPeriod,
    )
    serviceConfig.RegisterEventHandler(s.Proxier)
    go serviceConfig.Run(wait.NeverStop)
    
    // 配置端点处理器
    endpointsConfig := config.NewEndpointsConfig(
        informerFactory.Core().V1().Endpoints(),
        s.ConfigSyncPeriod,
    )
    endpointsConfig.RegisterEventHandler(s.Proxier)
    go endpointsConfig.Run(wait.NeverStop)
    
    // 启动定期同步
    go s.Proxier.SyncLoop()
    
    // 启动信息器工厂
    informerFactory.Start(wait.NeverStop)
    
    // 等待终止
    s.waitForTermination()
    
    return nil
}

// 7. Kubernetes调度器 - 将Pod分配给节点

// 调度器结构
type Scheduler struct {
    // 调度算法
    Algorithm ScheduleAlgorithm
    
    // 客户端
    Client clientset.Interface
    
    // Pod队列
    PodQueue internalqueue.SchedulingQueue
    
    // 各种Informer和Lister
    informerFactory informers.SharedInformerFactory
    podLister       corelisters.PodLister
    nodeLister      corelisters.NodeLister
    
    // 其他字段...
}

// 启动调度器
func (sched *Scheduler) Run(ctx context.Context) {
    // 启动所有Informer
    sched.informerFactory.Start(ctx.Done())
    
    // 等待缓存同步
    if !cache.WaitForCacheSync(ctx.Done(), sched.podLister.Informer().HasSynced, sched.nodeLister.Informer().HasSynced) {
        return
    }
    
    // 启动调度循环
    go wait.UntilWithContext(ctx, sched.scheduleOne, 0)
    
    <-ctx.Done()
}

// 调度单个Pod
func (sched *Scheduler) scheduleOne(ctx context.Context) {
    // 获取下一个Pod
    pod := sched.PodQueue.Pop()
    if pod == nil {
        return
    }
    
    // 尝试调度Pod
    start := time.Now()
    scheduleResult, err := sched.Algorithm.Schedule(ctx, pod)
    
    if err != nil {
        // 处理调度失败
        sched.handleSchedulingFailure(ctx, pod, err)
        return
    }
    
    // 处理调度成功
    nodeName := scheduleResult.SuggestedHost
    
    // 绑定Pod到节点
    err = sched.bindPod(ctx, pod, nodeName, scheduleResult.SchedulerExtender)
    if err != nil {
        log.Errorf("Error binding pod %v/%v: %v", pod.Namespace, pod.Name, err)
        return
    }
    
    // 发布成功事件
    sched.Recorder.Eventf(pod, nil, v1.EventTypeNormal, "Scheduled", "Successfully assigned %v/%v to %v", pod.Namespace, pod.Name, nodeName)
}

// 绑定Pod到节点
func (sched *Scheduler) bindPod(ctx context.Context, pod *v1.Pod, nodeName string, extender schedulerapi.ExtenderBindingArgs) error {
    binding := &v1.Binding{
        ObjectMeta: metav1.ObjectMeta{Namespace: pod.Namespace, Name: pod.Name, UID: pod.UID},
        Target:     v1.ObjectReference{Kind: "Node", Name: nodeName},
    }
    
    // 创建绑定
    err := sched.Client.CoreV1().Pods(pod.Namespace).Bind(ctx, binding, metav1.CreateOptions{})
    if err != nil {
        return err
    }
    
    return nil
}

// 8. CRD控制器 - 扩展Kubernetes

// 自定义资源定义控制器
type CRDController struct {
    // 客户端配置
    kubeClient clientset.Interface
    crdClient  apiextensionsclientset.Interface
    
    // 信息器
    crdInformer apiextensionslisters.CustomResourceDefinitionLister
    crdListerSynced cache.InformerSynced
    
    // 工作队列
    queue workqueue.RateLimitingInterface
    
    // 其他字段...
}

// 运行CRD控制器
func (c *CRDController) Run(workers int, stopCh <-chan struct{}) {
    defer utilruntime.HandleCrash()
    defer c.queue.ShutDown()
    
    log.Info("Starting CRD controller")
    defer log.Info("Shutting down CRD controller")
    
    // 等待缓存同步
    if !cache.WaitForCacheSync(stopCh, c.crdListerSynced) {
        return
    }
    
    // 启动工作线程
    for i := 0; i < workers; i++ {
        go wait.Until(c.worker, time.Second, stopCh)
    }
    
    <-stopCh
}

// 工作线程
func (c *CRDController) worker() {
    for c.processNextWorkItem() {
    }
}

// 处理工作项
func (c *CRDController) processNextWorkItem() bool {
    key, quit := c.queue.Get()
    if quit {
        return false
    }
    defer c.queue.Done(key)
    
    err := c.syncHandler(key.(string))
    if err != nil {
        c.queue.AddRateLimited(key)
        return true
    }
    
    c.queue.Forget(key)
    return true
}

// 同步CRD
func (c *CRDController) syncHandler(key string) error {
    namespace, name, err := cache.SplitMetaNamespaceKey(key)
    if err != nil {
        return err
    }
    
    // CRD是集群范围的资源，命名空间应该为空
    if namespace != "" {
        return fmt.Errorf("unexpected namespace in key: %q", key)
    }
    
    // 获取CRD
    crd, err := c.crdInformer.Get(name)
    if errors.IsNotFound(err) {
        // CRD已被删除，清理
        return c.handleCRDDeletion(name)
    }
    if err != nil {
        return err
    }
    
    // 处理CRD
    return c.handleCRD(crd)
}
```

**Kubernetes架构特点**：

- 声明式API设计
- 控制器模式实现自动化
- 分布式存储支持高可用
- 多层次网络抽象
- 容器作为基本组件
- 插件架构支持扩展
- 声明式配置管理

## 7. 新兴架构趋势

### 7.1 AI驱动的软件架构

-**基于LLM的软件架构**

```javascript
// AI驱动的应用架构示例

// 1. LLM作为核心决策引擎

// LLM客户端抽象
class LLMClient {
  constructor(config) {
    this.provider = config.provider; // 'openai', 'anthropic', 'local', etc.
    this.model = config.model;
    this.apiKey = config.apiKey;
    this.baseURL = config.baseURL;
    this.maxRetries = config.maxRetries || 3;
    this.timeout = config.timeout || 30000;
    
    // 初始化特定提供商的客户端
    this.client = this._initializeClient();
  }
  
  _initializeClient() {
    switch (this.provider) {
      case 'openai':
        return new OpenAIClient(this.apiKey, {
          baseURL: this.baseURL,
          maxRetries: this.maxRetries,
          timeout: this.timeout
        });
      case 'anthropic':
        return new AnthropicClient(this.apiKey, {
          baseURL: this.baseURL,
          maxRetries: this.maxRetries,
          timeout: this.timeout
        });
      case 'local':
        return new LocalLLMClient({
          modelPath: this.model,
          maxRetries: this.maxRetries,
          timeout: this.timeout
        });
      default:
        throw new Error(`Unsupported LLM provider: ${this.provider}`);
    }
  }
  
  async complete(prompt, options = {}) {
    try {
      return await this.client.complete(prompt, {
        temperature: options.temperature || 0.7,
        maxTokens: options.maxTokens,
        stopSequences: options.stopSequences,
        systemPrompt: options.systemPrompt,
        ...options
      });
    } catch (error) {
      console.error(`LLM completion error: ${error.message}`);
      throw error;
    }
  }
  
  async chat(messages, options = {}) {
    try {
      return await this.client.chat(messages, {
        temperature: options.temperature || 0.7,
        maxTokens: options.maxTokens,
        stopSequences: options.stopSequences,
        ...options
      });
    } catch (error) {
      console.error(`LLM chat error: ${error.message}`);
      throw error;
    }
  }
  
  async embedText(text) {
    try {
      return await this.client.embed(text);
    } catch (error) {
      console.error(`Text embedding error: ${error.message}`);
      throw error;
    }
  }
}

// 2. 语义路由和意图识别

class IntentRouter {
  constructor(llmClient, vectorStore) {
    this.llm = llmClient;
    this.vectorStore = vectorStore;
    this.intentHandlers = new Map();
    this.fallbackHandler = null;
    this.confidenceThreshold = 0.7;
  }
  
  registerIntent(intentName, handler, examples = []) {
    // 存储意图处理器
    this.intentHandlers.set(intentName, handler);
    
    // 如果提供了示例，创建意图嵌入向量
    if (examples.length > 0) {
      this._addExamplesToVectorStore(intentName, examples);
    }
  }
  
  setFallbackHandler(handler) {
    this.fallbackHandler = handler;
  }
  
  async _addExamplesToVectorStore(intentName, examples) {
    // 为每个示例创建嵌入并存储
    for (const example of examples) {
      const embedding = await this.llm.embedText(example);
      await this.vectorStore.addItem({
        id: `${intentName}-${Math.random().toString(36).substring(7)}`,
        vector: embedding,
        metadata: {
          intentName,
          example
        }
      });
    }
  }
  
  async route(userInput) {
    try {
      // 使用两种方法进行意图识别
      
      // 方法1: 向量相似性搜索
      const embedding = await this.llm.embedText(userInput);
      const similarItems = await this.vectorStore.search(embedding, 5);
      
      // 收集候选意图与其分数
      const candidates = {};
      for (const item of similarItems) {
        const { intentName } = item.metadata;
        if (!candidates[intentName]) {
          candidates[intentName] = { count: 0, score: 0 };
        }
        candidates[intentName].count++;
        candidates[intentName].score += item.similarity;
      }
      
      // 找出最佳意图
      let bestIntent = null;
      let highestScore = 0;
      
      for (const [intent, data] of Object.entries(candidates)) {
        const avgScore = data.score / data.count;
        if (avgScore > highestScore) {
          highestScore = avgScore;
          bestIntent = intent;
        }
      }
      
      // 方法2: 直接LLM分类（用于置信度低的情况）
      if (highestScore < this.confidenceThreshold) {
        // 构建意图分类提示
        const intents = Array.from(this.intentHandlers.keys());
        const prompt = `
          User input: "${userInput}"
          
          Select the most appropriate intent from the following list:
          ${intents.join(', ')}
          
          Reply with only the intent name, nothing else.
        `;
        
        const llmResponse = await this.llm.complete(prompt, {
          temperature: 0.2,
          maxTokens: 20
        });
        
        const predictedIntent = llmResponse.trim();
        
        // 如果LLM预测了有效意图，使用它
        if (this.intentHandlers.has(predictedIntent)) {
          bestIntent = predictedIntent;
          highestScore = 0.8; // 假设LLM的置信度
        }
      }
      
      // 执行找到的意图处理器或回退处理器
      if (bestIntent && highestScore >= this.confidenceThreshold) {
        const handler = this.intentHandlers.get(bestIntent);
        return await handler(userInput, { confidence: highestScore });
      } else if (this.fallbackHandler) {
        return await this.fallbackHandler(userInput, { candidates });
      } else {
        return {
          response: "I'm not sure I understand what you need. Could you please clarify?",
          intent: null,
          confidence: highestScore
        };
      }
    } catch (error) {
      console.error(`Intent routing error: ${error.message}`);
      throw error;
    }
  }
}

// 3. 向量数据库集成

class VectorStore {
  constructor(config) {
    this.provider = config.provider; // 'pinecone', 'qdrant', 'milvus', 'redis', 'local'
    this.dimension = config.dimension || 1536; // 默认OpenAI维度
    this.indexName = config.indexName;
    this.apiKey = config.apiKey;
    this.namespace = config.namespace;
    
```javascript
    // 初始化特定提供商的向量存储
    this.store = this._initializeVectorStore();
  }
  
  _initializeVectorStore() {
    switch (this.provider) {
      case 'pinecone':
        return new PineconeClient({
          apiKey: this.apiKey,
          indexName: this.indexName,
          namespace: this.namespace,
          dimension: this.dimension
        });
      case 'qdrant':
        return new QdrantClient({
          url: this.url,
          apiKey: this.apiKey,
          collectionName: this.indexName,
          dimension: this.dimension
        });
      case 'redis':
        return new RedisVectorClient({
          url: this.url,
          indexName: this.indexName,
          dimension: this.dimension
        });
      case 'local':
        return new LocalVectorStore({
          dimension: this.dimension
        });
      default:
        throw new Error(`Unsupported vector store provider: ${this.provider}`);
    }
  }
  
  async addItem({ id, vector, metadata = {} }) {
    return this.store.upsert({
      id,
      values: vector,
      metadata
    });
  }
  
  async search(vector, limit = 10, filters = {}) {
    return this.store.search({
      vector,
      limit,
      filters
    });
  }
  
  async deleteItem(id) {
    return this.store.delete(id);
  }
  
  async createIndex() {
    return this.store.createIndex({
      name: this.indexName,
      dimension: this.dimension
    });
  }
}

// 4. RAG系统实现

class RAGSystem {
  constructor(llmClient, vectorStore, documentProcessor) {
    this.llm = llmClient;
    this.vectorStore = vectorStore;
    this.documentProcessor = documentProcessor;
    this.maxContextLength = 3000; // 默认上下文长度限制
    this.retrievalConfig = {
      topK: 5,
      minRelevanceScore: 0.7
    };
  }
  
  async addDocuments(documents) {
    // 处理并索引文档
    for (const document of documents) {
      // 将文档分割成块
      const chunks = this.documentProcessor.splitDocument(document);
      
      // 为每个块创建嵌入并存储
      for (const chunk of chunks) {
        const embedding = await this.llm.embedText(chunk.text);
        await this.vectorStore.addItem({
          id: chunk.id,
          vector: embedding,
          metadata: {
            documentId: document.id,
            title: document.title,
            source: document.source,
            text: chunk.text,
            chunkIndex: chunk.index
          }
        });
      }
    }
  }
  
  async query(question, options = {}) {
    try {
      // 获取问题的嵌入
      const questionEmbedding = await this.llm.embedText(question);
      
      // 检索相关文档
      const retrievalResults = await this.vectorStore.search(
        questionEmbedding,
        options.topK || this.retrievalConfig.topK,
        options.filters || {}
      );
      
      // 过滤低相关性结果
      const relevantResults = retrievalResults.filter(
        result => result.similarity >= (options.minRelevanceScore || this.retrievalConfig.minRelevanceScore)
      );
      
      // 如果没有找到相关内容，返回无结果的回复
      if (relevantResults.length === 0) {
        return {
          answer: "I couldn't find any information related to your question.",
          sources: [],
          relevantDocuments: []
        };
      }
      
      // 构建上下文
      let context = '';
      const sources = new Set();
      const relevantDocuments = [];
      
      // 按相关性排序，添加到上下文，同时跟踪总长度
      for (const result of relevantResults) {
        const documentText = result.metadata.text;
        
        // 检查是否超出上下文长度限制
        if ((context.length + documentText.length) > this.maxContextLength) {
          continue;
        }
        
        // 添加到上下文
        context += `${documentText}\n\n`;
        
        // 添加到来源列表
        sources.add({
          documentId: result.metadata.documentId,
          title: result.metadata.title,
          source: result.metadata.source
        });
        
        // 添加到相关文档列表
        relevantDocuments.push({
          text: documentText,
          similarity: result.similarity,
          metadata: result.metadata
        });
      }
      
      // 构建提示
      const prompt = `
        Answer the following question based on the provided context. If the answer is not in the context, say "I don't have enough information to answer this question." Include only information from the context. Be concise and clear.
        
        Context:
        ${context}
        
        Question: ${question}
        
        Answer:
      `;
      
      // 调用LLM生成回答
      const response = await this.llm.complete(prompt, {
        temperature: options.temperature || 0.3,
        maxTokens: options.maxTokens || 500
      });
      
      return {
        answer: response.trim(),
        sources: Array.from(sources),
        relevantDocuments
      };
    } catch (error) {
      console.error(`RAG query error: ${error.message}`);
      throw error;
    }
  }
}

// 5. AI代理系统

class AIAgent {
  constructor(llmClient, tools = [], memory = null) {
    this.llm = llmClient;
    this.tools = new Map();
    this.memory = memory || new ShortTermMemory();
    this.maxIterations = 10;
    
    // 注册工具
    for (const tool of tools) {
      this.registerTool(tool);
    }
  }
  
  registerTool(tool) {
    this.tools.set(tool.name, tool);
  }
  
  async run(input, options = {}) {
    // 初始化会话状态
    const sessionState = {
      input,
      iterations: 0,
      intermediateSteps: [],
      toolResults: {},
      finalResponse: null
    };
    
    try {
      // 构建初始提示的系统指令
      const systemPrompt = this._buildSystemPrompt();
      
      // 获取过去的对话历史（如果有的话）
      const conversationHistory = await this.memory.getConversationHistory(options.sessionId);
      
      // 执行思考-行动-观察循环
      while (sessionState.iterations < this.maxIterations && !sessionState.finalResponse) {
        // 构建完整提示
        const messages = [
          { role: 'system', content: systemPrompt },
          ...conversationHistory,
          { role: 'user', content: sessionState.iterations === 0 ? input : "Continue from your previous actions." }
        ];
        
        // 添加之前的工具执行结果
        if (sessionState.intermediateSteps.length > 0) {
          for (const step of sessionState.intermediateSteps) {
            messages.push({ role: 'assistant', content: step.thought });
            messages.push({ 
              role: 'system', 
              content: `Action: ${step.action}\nAction Input: ${step.actionInput}\nObservation: ${step.observation}`
            });
          }
        }
        
        // 请求LLM的下一步思考
        const response = await this.llm.chat(messages, {
          temperature: options.temperature || 0.7,
          maxTokens: options.maxTokens || 1000
        });
        
        // 解析LLM响应
        const parsedResponse = this._parseAgentResponse(response);
        
        if (parsedResponse.finalAnswer) {
          // 代理决定了最终答案
          sessionState.finalResponse = parsedResponse.finalAnswer;
          break;
        } else if (parsedResponse.action) {
          // 代理想要执行工具
          const { action, actionInput } = parsedResponse;
          
          // 执行工具操作
          let observation = "Error: Tool not found";
          if (this.tools.has(action)) {
            try {
              const tool = this.tools.get(action);
              observation = await tool.run(actionInput);
            } catch (toolError) {
              observation = `Error executing tool: ${toolError.message}`;
            }
          }
          
          // 记录步骤
          sessionState.intermediateSteps.push({
            thought: parsedResponse.thought,
            action,
            actionInput,
            observation
          });
        } else {
          // 解析错误，引导代理回到正确的格式
          sessionState.intermediateSteps.push({
            thought: response,
            action: "invalid_format",
            actionInput: "",
            observation: "I couldn't understand your response. Please use the format specified in the instructions."
          });
        }
        
        sessionState.iterations++;
      }
      
      // 如果达到了最大迭代次数但没有最终答案
      if (!sessionState.finalResponse) {
        sessionState.finalResponse = "I've spent too much time trying to solve this problem. Here's what I've learned so far: " + 
          sessionState.intermediateSteps.map(step => step.observation).join(" ");
      }
      
      // 保存到记忆
      await this.memory.addToHistory(options.sessionId, { role: 'user', content: input });
      await this.memory.addToHistory(options.sessionId, { role: 'assistant', content: sessionState.finalResponse });
      
      return {
        response: sessionState.finalResponse,
        steps: sessionState.intermediateSteps,
        iterations: sessionState.iterations
      };
    } catch (error) {
      console.error(`Agent error: ${error.message}`);
      throw error;
    }
  }
  
  _buildSystemPrompt() {
    // 构建系统提示，包括代理说明和工具描述
    const toolDescriptions = Array.from(this.tools.values()).map(tool => {
      return `Tool Name: ${tool.name}\nDescription: ${tool.description}\nInput Parameters: ${tool.parameters}\n`;
    }).join('\n');
    
    return `
      You are an AI assistant that can use tools to help answer questions.
      
      To use a tool, please use the following format:
      
      Thought: <your reasoning about what to do>
      Action: <tool name>
      Action Input: <input parameters to the tool>
      
      After receiving the observation, you should continue with this format until you have enough information to provide a final answer.
      
      When you're ready to provide a final answer, use:
      
      Thought: <your final reasoning>
      Final Answer: <your answer to the user's question>
      
      Available Tools:
      ${toolDescriptions}
      
      Remember to:
      1. Think step-by-step
      2. Use tools whenever helpful
      3. Provide accurate, helpful and harmless responses
    `;
  }
  
  _parseAgentResponse(response) {
    // 解析代理的响应，提取思考、行动和最终答案
    const thought = response.match(/Thought: (.*?)(?=\nAction:|\nFinal Answer:|$)/s);
    const action = response.match(/Action: (.*?)(?=\nAction Input:|$)/s);
    const actionInput = response.match(/Action Input: (.*?)(?=\n|$)/s);
    const finalAnswer = response.match(/Final Answer: (.*?)(?=\n|$)/s);
    
    return {
      thought: thought ? thought[1].trim() : response,
      action: action ? action[1].trim() : null,
      actionInput: actionInput ? actionInput[1].trim() : null,
      finalAnswer: finalAnswer ? finalAnswer[1].trim() : null
    };
  }
}

// 6. 内存系统

class ShortTermMemory {
  constructor() {
    this.conversations = new Map();
    this.maxHistoryLength = 10;
  }
  
  async getConversationHistory(sessionId) {
    if (!sessionId) return [];
    return this.conversations.get(sessionId) || [];
  }
  
  async addToHistory(sessionId, message) {
    if (!sessionId) return;
    
    // 获取现有历史记录或创建新的
    const history = this.conversations.get(sessionId) || [];
    
    // 添加新消息
    history.push(message);
    
    // 如果历史记录太长，移除最早的消息
    while (history.length > this.maxHistoryLength) {
      history.shift();
    }
    
    // 更新历史记录
    this.conversations.set(sessionId, history);
  }
  
  async clearHistory(sessionId) {
    if (sessionId) {
      this.conversations.delete(sessionId);
    }
  }
}

class LongTermMemory {
  constructor(vectorStore) {
    this.vectorStore = vectorStore;
    this.encoder = new TextEncoder();
  }
  
  async saveMemory(memory) {
    // 为记忆创建嵌入
    const text = this._formatMemory(memory);
    const embedding = await this.llm.embedText(text);
    
    // 存储带有嵌入的记忆
    return this.vectorStore.addItem({
      id: memory.id || `memory-${Date.now()}-${Math.random().toString(36).substring(7)}`,
      vector: embedding,
      metadata: {
        ...memory,
        text,
        timestamp: memory.timestamp || new Date().toISOString()
      }
    });
  }
  
  async retrieveSimilarMemories(query, limit = 5) {
    // 获取查询的嵌入
    const embedding = await this.llm.embedText(query);
    
    // 搜索相似记忆
    return this.vectorStore.search(embedding, limit);
  }
  
  _formatMemory(memory) {
    // 将记忆对象格式化为文本
    if (typeof memory === 'string') {
      return memory;
    }
    
    let text = '';
    if (memory.type) text += `Type: ${memory.type}\n`;
    if (memory.content) text += `Content: ${memory.content}\n`;
    if (memory.context) text += `Context: ${memory.context}\n`;
    if (memory.timestamp) text += `Time: ${memory.timestamp}\n`;
    
    return text.trim();
  }
}

// 7. AI工作流引擎

class AIWorkflow {
  constructor(name, llmClient) {
    this.name = name;
    this.llm = llmClient;
    this.steps = [];
    this.currentStepIndex = 0;
    this.workflowContext = new Map();
  }
  
  addStep(step) {
    this.steps.push(step);
    return this;
  }
  
  setContext(key, value) {
    this.workflowContext.set(key, value);
    return this;
  }
  
  getContext(key) {
    return this.workflowContext.get(key);
  }
  
  async execute(initialInput, options = {}) {
    // 重置工作流状态
    this.currentStepIndex = 0;
    this.workflowContext.clear();
    
    // 设置初始输入
    let currentInput = initialInput;
    
    // 执行步骤
    const stepResults = [];
    
    try {
      while (this.currentStepIndex < this.steps.length) {
        const currentStep = this.steps[this.currentStepIndex];
        
        // 执行当前步骤
        const stepResult = await currentStep.execute(currentInput, this.workflowContext, this.llm);
        
        // 保存步骤结果
        stepResults.push({
          stepName: currentStep.name,
          input: currentInput,
          output: stepResult.output,
          metadata: stepResult.metadata
        });
        
        // 如果步骤指定了跳转，更新下一步索引
        if (stepResult.nextStep !== undefined) {
          // 查找名称匹配的步骤
          const nextStepIndex = this.steps.findIndex(step => step.name === stepResult.nextStep);
          if (nextStepIndex !== -1) {
            this.currentStepIndex = nextStepIndex;
          } else {
            // 如果没有找到匹配的步骤名称，尝试解析为数字索引
            const numericIndex = parseInt(stepResult.nextStep, 10);
            if (!isNaN(numericIndex) && numericIndex >= 0 && numericIndex < this.steps.length) {
              this.currentStepIndex = numericIndex;
            } else {
              // 默认移动到下一步
              this.currentStepIndex++;
            }
          }
        } else {
          // 默认移动到下一步
          this.currentStepIndex++;
        }
        
        // 更新下一步的输入
        currentInput = stepResult.output;
      }
      
      return {
        status: 'completed',
        output: currentInput, // 最后一步的输出作为工作流输出
        stepResults,
        context: Object.fromEntries(this.workflowContext)
      };
    } catch (error) {
      console.error(`Workflow execution error at step ${this.currentStepIndex}: ${error.message}`);
      
      return {
        status: 'failed',
        error: error.message,
        stepIndex: this.currentStepIndex,
        stepName: this.steps[this.currentStepIndex]?.name,
        stepResults,
        context: Object.fromEntries(this.workflowContext)
      };
    }
  }
}

// 工作流步骤基类
class WorkflowStep {
  constructor(name) {
    this.name = name;
  }
  
  async execute(input, context, llm) {
    throw new Error('Method execute() must be implemented by subclass');
  }
}

// LLM处理步骤
class LLMProcessingStep extends WorkflowStep {
  constructor(name, prompt, options = {}) {
    super(name);
    this.promptTemplate = prompt;
    this.options = options;
  }
  
  async execute(input, context, llm) {
    // 编译提示模板，替换变量
    const compiledPrompt = this._compileTemplate(this.promptTemplate, { input, context });
    
    // 调用LLM
    const response = await llm.complete(compiledPrompt, this.options);
    
    return {
      output: response,
      metadata: {
        prompt: compiledPrompt,
        options: this.options
      }
    };
  }
  
  _compileTemplate(template, data) {
    return template.replace(/\{\{(.*?)\}\}/g, (match, variable) => {
      const path = variable.trim().split('.');
      let value;
      
      if (path[0] === 'input') {
        value = data.input;
      } else if (path[0] === 'context') {
        value = data.context.get(path[1]);
      }
      
      return value !== undefined ? value : match;
    });
  }
}

// 条件分支步骤
class ConditionalStep extends WorkflowStep {
  constructor(name, conditionFn, trueStepName, falseStepName) {
    super(name);
    this.conditionFn = conditionFn;
    this.trueStepName = trueStepName;
    this.falseStepName = falseStepName;
  }
  
  async execute(input, context, llm) {
    // 评估条件
    const conditionResult = await this.conditionFn(input, context, llm);
    
    // 根据条件确定下一步
    const nextStep = conditionResult ? this.trueStepName : this.falseStepName;
    
    return {
      output: input, // 条件步骤通常不修改输入
      nextStep,
      metadata: {
        conditionResult
      }
    };
  }
}

// 函数执行步骤
class FunctionStep extends WorkflowStep {
  constructor(name, fn) {
    super(name);
    this.fn = fn;
  }
  
  async execute(input, context, llm) {
    // 执行函数
    const result = await this.fn(input, context, llm);
    
    return {
      output: result.output !== undefined ? result.output : input,
      nextStep: result.nextStep,
      metadata: result.metadata || {}
    };
  }
}

// 8. 应用示例 - 智能客户支持系统

// 初始化核心组件
const llmClient = new LLMClient({
  provider: 'openai',
  model: 'gpt-4',
  apiKey: process.env.OPENAI_API_KEY
});

const vectorStore = new VectorStore({
  provider: 'pinecone',
  indexName: 'customer-support-kb',
  apiKey: process.env.PINECONE_API_KEY,
  dimension: 1536 // OpenAI嵌入维度
});

// 初始化内存系统
const shortTermMemory = new ShortTermMemory();
const longTermMemory = new LongTermMemory(vectorStore);

// 初始化知识库
const ragSystem = new RAGSystem(llmClient, vectorStore, {
  splitDocument: (doc) => {
    // 简化的文档分割逻辑
    const chunks = [];
    const paragraphs = doc.content.split('\n\n');
    for (let i = 0; i < paragraphs.length; i++) {
      chunks.push({
        id: `${doc.id}-chunk-${i}`,
        text: paragraphs[i],
        index: i
      });
    }
    return chunks;
  }
});

// 定义工具
const tools = [
  {
    name: 'search_knowledge_base',
    description: 'Search for information in the knowledge base',
    parameters: 'query: string - The search query',
    run: async (query) => {
      const result = await ragSystem.query(query);
      return result.answer;
    }
  },
  {
    name: 'get_customer_info',
    description: 'Get customer information from the CRM',
    parameters: 'customerId: string - The customer ID',
    run: async (customerId) => {
      // 实际实现将连接到CRM
      return JSON.stringify({
        id: customerId,
        name: 'Example Customer',
        plan: 'Enterprise',
        supportLevel: 'Premium',
        recentTickets: 2
      });
    }
  },
  {
    name: 'create_support_ticket',
    description: 'Create a new customer support ticket',
    parameters: 'JSON object with {customerId, title, description, priority}',
    run: async (params) => {
      // 解析JSON
      const ticketData = typeof params === 'string' ? JSON.parse(params) : params;
      
      // 实际实现将连接到工单系统
      const ticketId = `TICKET-${Date.now().toString().substring(7)}`;
      return `Ticket created successfully. Ticket ID: ${ticketId}`;
    }
  }
];

// 初始化意图路由器
const intentRouter = new IntentRouter(llmClient, vectorStore);

// 注册意图处理器
intentRouter.registerIntent('product_info', async (input, context) => {
  const result = await ragSystem.query(input, { 
    filters: { metadata: { category: 'product' } }
  });
  return { response: result.answer, intent: 'product_info' };
}, [
  'What features does your product have?',
  'Can you tell me about your pricing plans?',
  'What are the system requirements?',
  'How do I install the software?'
]);

intentRouter.registerIntent('technical_support', async (input, context) => {
  // 这里我们使用AI代理来处理技术支持问题
  const agent = new AIAgent(llmClient, tools, shortTermMemory);
  const result = await agent.run(input, { sessionId: context.sessionId });
  return { response: result.response, intent: 'technical_support' };
}, [
  'I'm having trouble logging in',
  'The system is showing an error',
  'How do I reset my password?',
  'My account is locked'
]);

intentRouter.registerIntent('billing', async (input, context) => {
  // 使用工作流处理账单问题
  const billingWorkflow = new AIWorkflow('billing_inquiry', llmClient)
    .addStep(new LLMProcessingStep('analyze_question', 
      `Analyze this billing related question and determine what specific information is needed: {{input}}`
    ))
    .addStep(new ConditionalStep('check_customer_id',
      (input, context) => context.has('customerId'),
      'get_billing_info',
      'request_customer_id'
    ))
    .addStep(new LLMProcessingStep('request_customer_id',
      `The user has a billing question but we need their customer ID. Politely ask: {{input}}`
    ))
    .addStep(new FunctionStep('get_billing_info', async (input, context) => {
      const customerId = context.get('customerId');
      // 这里应该连接到实际的账单系统
      const billingInfo = {
        customerId,
        currentPlan: 'Enterprise',
        nextBillingDate: '2023-12-01',
        lastPayment: { amount: '$1999', date: '2023-11-01' }
      };
      context.set('billingInfo', billingInfo);
      return { output: input };
    }))
    .addStep(new LLMProcessingStep('formulate_response',
      `Based on the user's billing question: {{input}}
       
       And their billing information: {{context.billingInfo}}
       
       Provide a helpful, personalized response that answers their specific question.`
    ));
    
  const result = await billingWorkflow.execute(input, { 
    sessionId: context.sessionId,
    customerId: context.customerId 
  });
  
  return { response: result.output, intent: 'billing' };
}, [
  'When is my next bill due?',
  'How much did I pay last month?',
  'Can I update my payment method?',
  'I think I was overcharged'
]);

// 设置回退处理器
intentRouter.setFallbackHandler(async (input, context) => {
  // 使用RAG系统尝试找到相关信息
  const result = await ragSystem.query(input);
  if (result.relevantDocuments.length > 0) {
    return { response: result.answer, intent: 'general_information' };
  } else {
    // 如果没有找到相关信息，使用LLM生成基于常识的回复
    const response = await llmClient.complete(
      `As a customer support agent, please provide a helpful response to this query: ${input}`, 
      { temperature: 0.7 }
    );
    return { response, intent: 'general_conversation' };
  }
});

// 主要处理函数
async function handleCustomerQuery(query, sessionId, customerInfo = {}) {
  try {
    // 创建上下文
    const context = {
      sessionId,
      ...customerInfo
    };
    
    // 路由到适当的意图
    const result = await intentRouter.route(query, context);
    
    // 保存对话到内存
    await shortTermMemory.addToHistory(sessionId, { role: 'user', content: query });
    await shortTermMemory.addToHistory(sessionId, { role: 'assistant', content: result.response });
    
    // 如果是重要交互，保存到长期记忆
    if (result.intent === 'technical_support' || result.intent === 'billing') {
      await longTermMemory.saveMemory({
        type: 'customer_interaction',
        content: query,
        response: result.response,
        intent: result.intent,
        customerId: customerInfo.customerId,
        timestamp: new Date().toISOString()
      });
    }
    
    return result;
  } catch (error) {
    console.error(`Error handling customer query: ${error.message}`);
    return {
      response: "I'm having trouble processing your request right now. Please try again later or contact our support team directly.",
      intent: 'error',
      error: error.message
    };
  }
}
```

**AI驱动架构特点**：

- LLM作为自然语言接口和决策引擎
- 向量数据库支持语义搜索
- RAG系统结合知识库和生成能力
- 意图识别实现智能路由
- AI代理支持复杂任务分解和工具使用
- 工作流引擎协调多步骤处理
- 短期和长期记忆系统管理上下文

### 7.2 WebAssembly应用架构

-**WebAssembly应用架构**

```javascript
// WebAssembly应用架构示例

// 1. WebAssembly模块加载和初始化

// 异步加载模块的辅助函数
async function loadWasmModule(wasmUrl, importObject = {}) {
  try {
    // 获取.wasm文件
    const response = await fetch(wasmUrl);
    
    // 判断响应是否正常
    if (!response.ok) {
      throw new Error(`Failed to fetch ${wasmUrl}: ${response.status} ${response.statusText}`);
    }
    
    // 将响应转换为ArrayBuffer
    const bytes = await response.arrayBuffer();
    
    // 编译WebAssembly模块
    const module = await WebAssembly.compile(bytes);

    // 实例化模块
    const instance = await WebAssembly.instantiate(module, importObject);
    
    return {
      module,
      instance,
      exports: instance.exports
    };
  } catch (error) {
    console.error("Failed to load WebAssembly module:", error);
    throw error;
  }
}

// 2. JavaScript与WebAssembly的内存交互

class WasmMemoryManager {
  constructor(memory, exports) {
    this.memory = memory;
    this.exports = exports;
    this.allocator = exports.__alloc || exports.alloc || exports.malloc;
    this.deallocator = exports.__dealloc || exports.dealloc || exports.free;
    
    if (!this.allocator) {
      throw new Error("No memory allocator function found in WebAssembly exports");
    }
  }
  
  // 从JavaScript字符串创建WebAssembly字符串
  createString(str) {
    const bytes = new TextEncoder().encode(str + '\0'); // 包含null终止符
    const ptr = this.allocator(bytes.length);
    
    const heap = new Uint8Array(this.memory.buffer);
    heap.set(bytes, ptr);
    
    return {
      ptr,
      length: bytes.length - 1, // 不包括null终止符
      free: () => this.deallocator(ptr)
    };
  }
  
  // 从WebAssembly内存中读取字符串
  readString(ptr, length) {
    const heap = new Uint8Array(this.memory.buffer);
    
    // 如果没有提供长度，查找null终止符
    if (length === undefined) {
      length = 0;
      while (heap[ptr + length] !== 0) length++;
    }
    
    const bytes = heap.slice(ptr, ptr + length);
    return new TextDecoder().decode(bytes);
  }
  
  // 创建WebAssembly数值数组
  createArray(array, type = Float64Array) {
    const bytes = array.length * type.BYTES_PER_ELEMENT;
    const ptr = this.allocator(bytes);
    
    const heap = new type(this.memory.buffer);
    // 写入数组数据
    for (let i = 0; i < array.length; i++) {
      heap[ptr / type.BYTES_PER_ELEMENT + i] = array[i];
    }
    
    return {
      ptr,
      length: array.length,
      free: () => this.deallocator(ptr)
    };
  }
  
  // 从WebAssembly内存中读取数值数组
  readArray(ptr, length, type = Float64Array) {
    const heap = new type(this.memory.buffer);
    const result = new type(length);
    
    for (let i = 0; i < length; i++) {
      result[i] = heap[ptr / type.BYTES_PER_ELEMENT + i];
    }
    
    return result;
  }
}

// 3. 模块化WebAssembly应用架构

class WasmModule {
  constructor(name) {
    this.name = name;
    this.instance = null;
    this.exports = null;
    this.memory = null;
    this.memoryManager = null;
    this.isLoaded = false;
    this.importObject = {};
    this.dependencies = [];
  }
  
  // 添加JS环境提供给WebAssembly的导入函数
  addImports(namespace, imports) {
    if (!this.importObject[namespace]) {
      this.importObject[namespace] = {};
    }
    
    Object.assign(this.importObject[namespace], imports);
    return this;
  }
  
  // 添加依赖的模块
  addDependency(module) {
    this.dependencies.push(module);
    return this;
  }
  
  // 加载模块
  async load(wasmUrl) {
    try {
      // 确保所有依赖已加载
      for (const dep of this.dependencies) {
        if (!dep.isLoaded) {
          await dep.waitUntilLoaded();
        }
        
        // 将依赖的导出添加到导入对象中
        this.addImports(dep.name, dep.exports);
      }
      
      // 加载WebAssembly模块
      const result = await loadWasmModule(wasmUrl, this.importObject);
      
      this.instance = result.instance;
      this.exports = result.exports;
      
      // 获取内存
      this.memory = this.exports.memory || this.importObject.env?.memory;
      
      if (!this.memory) {
        throw new Error("No memory found in WebAssembly instance or imports");
      }
      
      // 创建内存管理器
      this.memoryManager = new WasmMemoryManager(this.memory, this.exports);
      
      this.isLoaded = true;
      
      // 如果有初始化函数，调用它
      if (typeof this.exports._initialize === 'function') {
        this.exports._initialize();
      }
      
      return this;
    } catch (error) {
      console.error(`Failed to load WebAssembly module '${this.name}':`, error);
      throw error;
    }
  }
  
  // 等待模块加载完成
  waitUntilLoaded() {
    return new Promise((resolve, reject) => {
      const check = () => {
        if (this.isLoaded) {
          resolve(this);
        } else {
          setTimeout(check, 10);
        }
      };
      check();
    });
  }
  
  // 将JS函数暴露给WebAssembly
  exposeFunction(name, fn) {
    if (!this.importObject.env) {
      this.importObject.env = {};
    }
    
    this.importObject.env[name] = fn;
    return this;
  }
}

// 4. 复杂WebAssembly应用示例 - 图像处理应用

class ImageProcessor {
  constructor() {
    this.modules = {
      core: new WasmModule('core'),
      filters: new WasmModule('filters'),
      transforms: new WasmModule('transforms')
    };
    
    // 设置模块依赖关系
    this.modules.filters.addDependency(this.modules.core);
    this.modules.transforms.addDependency(this.modules.core);
    
    // 添加JS环境函数
    this._setupEnvironment();
  }
  
  // 设置JS环境函数
  _setupEnvironment() {
    // 添加日志函数
    this.modules.core.exposeFunction('console_log', (ptr) => {
      if (!this.modules.core.memoryManager) return;
      const message = this.modules.core.memoryManager.readString(ptr);
      console.log(`[WASM] ${message}`);
    });
    
    // 添加性能测量函数
    let perfMarks = {};
    
    this.modules.core.exposeFunction('perf_mark', (namePtr) => {
      if (!this.modules.core.memoryManager) return;
      const name = this.modules.core.memoryManager.readString(namePtr);
      perfMarks[name] = performance.now();
    });
    
    this.modules.core.exposeFunction('perf_measure', (startPtr, endPtr) => {
      if (!this.modules.core.memoryManager) return 0;
      const startName = this.modules.core.memoryManager.readString(startPtr);
      const endName = this.modules.core.memoryManager.readString(endPtr);
      
      if (!perfMarks[startName] || !perfMarks[endName]) {
        return 0;
      }
      
      return perfMarks[endName] - perfMarks[startName];
    });
  }
  
  // 加载所有模块
  async initialize() {
    // 加载核心模块
    await this.modules.core.load('/wasm/image_core.wasm');
    
    // 并行加载其他模块
    await Promise.all([
      this.modules.filters.load('/wasm/image_filters.wasm'),
      this.modules.transforms.load('/wasm/image_transforms.wasm')
    ]);
    
    console.log('All WebAssembly modules loaded successfully');
    return this;
  }
  
  // 处理图像
  async processImage(imageData, operations) {
    if (!this.modules.core.isLoaded) {
      throw new Error('Image processor not initialized');
    }
    
    try {
      // 将图像数据复制到WebAssembly内存
      const width = imageData.width;
      const height = imageData.height;
      const pixelData = new Uint8ClampedArray(imageData.data);
      
      // 分配内存
      const pixelDataPtr = this.modules.core.exports.allocate_image_buffer(width * height * 4);
      
      // 复制数据
      new Uint8ClampedArray(this.modules.core.memory.buffer).set(pixelData, pixelDataPtr);
      
      // 创建图像处理上下文
      const contextPtr = this.modules.core.exports.create_image_context(pixelDataPtr, width, height);
      
      // 按顺序应用操作
      for (const op of operations) {
        switch (op.type) {
          case 'filter':
            await this._applyFilter(contextPtr, op.name, op.params);
            break;
          case 'transform':
            await this._applyTransform(contextPtr, op.name, op.params);
            break;
          default:
            console.warn(`Unknown operation type: ${op.type}`);
        }
      }
      
      // 获取处理后的图像数据
      const resultPtr = this.modules.core.exports.get_image_data(contextPtr);
      const resultData = new Uint8ClampedArray(
        this.modules.core.memory.buffer,
        resultPtr,
        width * height * 4
      );
      
      // 创建新的ImageData对象
      const result = new ImageData(
        new Uint8ClampedArray(resultData),
        width,
        height
      );
      
      // 清理分配的内存
      this.modules.core.exports.destroy_image_context(contextPtr);
      
      return result;
    } catch (error) {
      console.error('Error processing image:', error);
      throw error;
    }
  }
  
  // 应用滤镜
  async _applyFilter(contextPtr, filterName, params = {}) {
    const filters = this.modules.filters.exports;
    
    switch (filterName) {
      case 'grayscale':
        filters.apply_grayscale(contextPtr);
        break;
      case 'sepia':
        filters.apply_sepia(contextPtr);
        break;
      case 'blur':
        const radius = params.radius || 3;
        filters.apply_blur(contextPtr, radius);
        break;
      case 'sharpen':
        const amount = params.amount || 1.0;
        filters.apply_sharpen(contextPtr, amount);
        break;
      case 'brightness':
        const factor = params.factor || 1.0;
        filters.adjust_brightness(contextPtr, factor);
        break;
      case 'contrast':
        const level = params.level || 1.0;
        filters.adjust_contrast(contextPtr, level);
        break;
      default:
        console.warn(`Unknown filter: ${filterName}`);
    }
  }
  
  // 应用变换
  async _applyTransform(contextPtr, transformName, params = {}) {
    const transforms = this.modules.transforms.exports;
    
    switch (transformName) {
      case 'rotate':
        const angle = params.angle || 0;
        transforms.rotate_image(contextPtr, angle);
        break;
      case 'flip':
        const horizontal = params.horizontal || false;
        const vertical = params.vertical || false;
        transforms.flip_image(contextPtr, horizontal, vertical);
        break;
      case 'resize':
        const newWidth = params.width || 0;
        const newHeight = params.height || 0;
        transforms.resize_image(contextPtr, newWidth, newHeight);
        break;
      case 'crop':
        const x = params.x || 0;
        const y = params.y || 0;
        const width = params.width || 0;
        const height = params.height || 0;
        transforms.crop_image(contextPtr, x, y, width, height);
        break;
      default:
        console.warn(`Unknown transform: ${transformName}`);
    }
  }
}

// 5. WebAssembly Thread管理

class WasmThreadPool {
  constructor(wasmUrl, numThreads) {
    this.wasmUrl = wasmUrl;
    this.numThreads = numThreads;
    this.workers = [];
    this.taskQueue = [];
    this.nextTaskId = 1;
    this.activeWorkers = 0;
  }
  
  async initialize() {
    // 检查是否支持SharedArrayBuffer
    if (typeof SharedArrayBuffer === 'undefined') {
      throw new Error('SharedArrayBuffer is not supported in this browser');
    }
    
    // 创建Web Workers
    for (let i = 0; i < this.numThreads; i++) {
      const worker = new Worker('/js/wasm-worker.js');
      
      // 设置worker消息处理
      worker.onmessage = (event) => this._handleWorkerMessage(worker, event);
      
      // 初始化worker
      await new Promise((resolve, reject) => {
        worker.onmessage = (event) => {
          if (event.data.type === 'initialized') {
            worker.onmessage = (event) => this._handleWorkerMessage(worker, event);
            resolve();
          } else if (event.data.type === 'error') {
            reject(new Error(event.data.message));
          }
        };
        
        worker.postMessage({
          type: 'initialize',
          wasmUrl: this.wasmUrl
        });
      });
      
      this.workers.push({
        worker,
        busy: false
      });
    }
    
    console.log(`WebAssembly Thread Pool initialized with ${this.numThreads} workers`);
    return this;
  }
  
  // 提交任务
  submitTask(taskType, taskData) {
    return new Promise((resolve, reject) => {
      const taskId = this.nextTaskId++;
      
      this.taskQueue.push({
        id: taskId,
        type: taskType,
        data: taskData,
        resolve,
        reject
      });
      
      // 尝试调度任务
      this._scheduleTasks();
    });
  }
  
  // 处理worker消息
  _handleWorkerMessage(worker, event) {
    const { type, taskId, result, error } = event.data;
    
    // 查找对应的worker
    const workerInfo = this.workers.find(w => w.worker === worker);
    
    if (!workerInfo) {
      console.error('Received message from unknown worker');
      return;
    }
    
    if (type === 'task_complete') {
      // 查找任务
      const task = this.taskQueue.find(t => t.id === taskId);
      
      if (task) {
        // 从队列中移除任务
        this.taskQueue = this.taskQueue.filter(t => t.id !== taskId);
        
        // 解决promise
        if (error) {
          task.reject(new Error(error));
        } else {
          task.resolve(result);
        }
      }
      
      // 设置worker为空闲
      workerInfo.busy = false;
      this.activeWorkers--;
      
      // 调度更多任务
      this._scheduleTasks();
    }
  }
  
  // 调度待处理任务
  _scheduleTasks() {
    // 获取所有空闲worker
    const idleWorkers = this.workers.filter(w => !w.busy);
    
    // 为每个空闲worker分配任务
    for (const workerInfo of idleWorkers) {
      // 如果没有更多任务，跳出循环
      if (this.taskQueue.length === 0) break;
      
      // 获取下一个任务
      const nextTask = this.taskQueue.find(t => !t.assigned);
      
      if (nextTask) {
        // 标记任务为已分配
        nextTask.assigned = true;
        
        // 设置worker为忙碌状态
        workerInfo.busy = true;
        this.activeWorkers++;
        
        // 发送任务到worker
        workerInfo.worker.postMessage({
          type: 'task',
          taskId: nextTask.id,
          taskType: nextTask.type,
          taskData: nextTask.data
        });
      }
    }
  }
  
  // 获取活跃工作线程数量
  getActiveCount() {
    return this.activeWorkers;
  }
  
  // 获取待处理任务数量
  getPendingCount() {
    return this.taskQueue.filter(t => !t.assigned).length;
  }
  
  // 关闭线程池
  terminate() {
    for (const { worker } of this.workers) {
      worker.terminate();
    }
    
    this.workers = [];
    
    // 拒绝所有待处理任务
    for (const task of this.taskQueue) {
      task.reject(new Error('Thread pool terminated'));
    }
    
    this.taskQueue = [];
    this.activeWorkers = 0;
  }
}

// WebAssembly Worker实现 (wasm-worker.js)
// 这部分代码将作为单独的worker文件存在
let wasmModule = null;
let wasmExports = null;
let wasmMemory = null;

self.onmessage = async function(event) {
  const { type, taskId, taskType, taskData, wasmUrl } = event.data;
  
  try {
    if (type === 'initialize') {
      await initializeWasm(wasmUrl);
      
      self.postMessage({ type: 'initialized' });
    } else if (type === 'task') {
      if (!wasmExports) {
        throw new Error('WebAssembly module not initialized');
      }
      
      // 执行任务
      const result = await executeTask(taskType, taskData);
      
      // 返回结果
      self.postMessage({
        type: 'task_complete',
        taskId,
        result
      });
    }
  } catch (error) {
    self.postMessage({
      type: 'error',
      taskId,
      error: error.message
    });
  }
};

// 初始化WebAssembly模块
async function initializeWasm(wasmUrl) {
  // 获取.wasm文件
  const response = await fetch(wasmUrl);
  
  if (!response.ok) {
    throw new Error(`Failed to fetch ${wasmUrl}: ${response.status}`);
  }
  
  // 编译模块
  const bytes = await response.arrayBuffer();
  const module = await WebAssembly.compile(bytes);
  
  // 创建内存
  wasmMemory = new WebAssembly.Memory({ initial: 10, maximum: 100, shared: true });
  
  // 实例化模块
  const instance = await WebAssembly.instantiate(module, {
    env: {
      memory: wasmMemory,
      consoleLog: (ptr) => {
        const heap = new Uint8Array(wasmMemory.buffer);
        let str = '';
        let i = ptr;
        while (heap[i] !== 0) {
          str += String.fromCharCode(heap[i]);
          i++;
        }
        console.log(`[WASM Worker] ${str}`);
      }
    }
  });
  
  wasmModule = module;
  wasmExports = instance.exports;
}

// 执行任务
async function executeTask(taskType, taskData) {
  switch (taskType) {
    case 'process_chunk':
      return processChunk(taskData);
    case 'compute_hash':
      return computeHash(taskData);
    // 其他任务类型...
    default:
      throw new Error(`Unknown task type: ${taskType}`);
  }
}

// 处理数据块
function processChunk(data) {
  // 将数据复制到WebAssembly内存
  const { buffer, offset, length, params } = data;
  
  // 分配内存
  const inputPtr = wasmExports.malloc(length);
  
  // 复制数据
  new Uint8Array(wasmMemory.buffer).set(new Uint8Array(buffer), inputPtr);
  
  // 处理数据
  const outputPtr = wasmExports.process_data_chunk(
    inputPtr, 
    length, 
    params.option1, 
    params.option2
  );
  
  // 读取结果
  const outputLength = wasmExports.get_result_length();
  const result = new Uint8Array(
    wasmMemory.buffer.slice(
      outputPtr, 
      outputPtr + outputLength
    )
  );
  
  // 释放内存
  wasmExports.free(inputPtr);
  wasmExports.free(outputPtr);
  
  return result;
}

// 计算哈希值
function computeHash(data) {
  const { buffer } = data;
  
  // 分配内存
  const inputPtr = wasmExports.malloc(buffer.byteLength);
  
  // 复制数据
  new Uint8Array(wasmMemory.buffer).set(new Uint8Array(buffer), inputPtr);
  
  // 计算哈希
  const hashPtr = wasmExports.compute_hash(inputPtr, buffer.byteLength);
  
  // 读取哈希值
  const hashLength = 32; // 假设是SHA-256
  const hashResult = new Uint8Array(
    wasmMemory.buffer.slice(
      hashPtr, 
      hashPtr + hashLength
    )
  );
  
  // 转换为十六进制
  const hashHex = Array.from(hashResult)
    .map(b => b.toString(16).padStart(2, '0'))
    .join('');
  
  // 释放内存
  wasmExports.free(inputPtr);
  
  return hashHex;
}
*/

// 6. WebAssembly与WebGL集成

class WasmWebGLRenderer {
  constructor() {
    this.canvas = null;
    this.gl = null;
    this.wasmModule = new WasmModule('renderer');
    this.program = null;
    this.attributes = {};
    this.uniforms = {};
    this.textures = {};
  }
  
  async initialize(canvas) {
    this.canvas = canvas;
    
    // 初始化WebGL上下文
    this.gl = canvas.getContext('webgl2');
    
    if (!this.gl) {
      throw new Error('WebGL 2 is not supported by your browser');
    }
    
    // 加载WebAssembly模块
    await this.wasmModule
      .exposeFunction('gl_create_shader', (typePtr, sourcePtr) => {
        const type = this.wasmModule.memoryManager.readString(typePtr);
        const source = this.wasmModule.memoryManager.readString(sourcePtr);
        
        return this._createShader(type, source);
      })
      .exposeFunction('gl_create_program', (vertexShader, fragmentShader) => {
        return this._createProgram(vertexShader, fragmentShader);
      })
      .exposeFunction('gl_get_attrib_location', (programId, namePtr) => {
        const name = this.wasmModule.memoryManager.readString(namePtr);
        return this.gl.getAttribLocation(programId, name);
      })
      .exposeFunction('gl_get_uniform_location', (programId, namePtr) => {
        const name = this.wasmModule.memoryManager.readString(namePtr);
        return this.gl.getUniformLocation(programId, name);
      })
      .exposeFunction('gl_create_buffer', () => {
        return this.gl.createBuffer();
      })
      .exposeFunction('gl_buffer_data', (buffer, dataPtr, size, usage) => {
        const data = new Float32Array(
          this.wasmModule.memory.buffer.slice(dataPtr, dataPtr + size * 4)
        );
        this.gl.bindBuffer(this.gl.ARRAY_BUFFER, buffer);
        this.gl.bufferData(this.gl.ARRAY_BUFFER, data, usage);
      })
      .load('/wasm/webgl_renderer.wasm');
    
    // 初始化渲染器
    const result = this.wasmModule.exports.initialize_renderer(
      canvas.width,
      canvas.height
    );
    
    if (result !== 0) {
      throw new Error(`Failed to initialize WASM WebGL renderer: ${result}`);
    }
    
    // 获取着色器程序
    this.program = this.wasmModule.exports.get_shader_program();
    
    // 设置属性和uniform
    this._setupAttributes();
    this._setupUniforms();
    
    console.log('WebAssembly WebGL Renderer initialized successfully');
    
    return this;
  }
  
  // 设置场景
  setupScene(sceneData) {
    // 将场景数据传递给WebAssembly
    const { vertices, indices, textures } = sceneData;
    
    // 分配和复制顶点数据
    const verticesArray = this.wasmModule.memoryManager.createArray(
      new Float32Array(vertices)
    );
    
    // 分配和复制索引数据
    const indicesArray = this.wasmModule.memoryManager.createArray(
      new Uint16Array(indices),
      Uint16Array
    );
    
    // 设置场景
    this.wasmModule.exports.setup_scene(
      verticesArray.ptr,
      verticesArray.length,
      indicesArray.ptr,
      indicesArray.length
    );
    
    // 清理内存
    verticesArray.free();
    indicesArray.free();
    
    // 加载纹理
    this._loadTextures(textures);
  }
  
  // 加载纹理
  async _loadTextures(textureList) {
    for (const texInfo of textureList) {
      // 加载图像
      const image = await this._loadImage(texInfo.url);
      
      // 创建WebGL纹理
      const texture = this.gl.createTexture();
      this.gl.bindTexture(this.gl.TEXTURE_2D, texture);
      
      // 设置参数
      this.gl.texParameteri(this.gl.TEXTURE_2D, this.gl.TEXTURE_WRAP_S, this.gl.CLAMP_TO_EDGE);
      this.gl.texParameteri(this.gl.TEXTURE_2D, this.gl.TEXTURE_WRAP_T, this.gl.CLAMP_TO_EDGE);
      this.gl.texParameteri(this.gl.TEXTURE_2D, this.gl.TEXTURE_MIN_FILTER, this.gl.LINEAR);
      this.gl.texParameteri(this.gl.TEXTURE_2D, this.gl.TEXTURE_MAG_FILTER, this.gl.LINEAR);
      
      // 上传图像数据
      this.gl.texImage2D(
        this.gl.TEXTURE_2D,
        0,
        this.gl.RGBA,
        this.gl.RGBA,
        this.gl.UNSIGNED_BYTE,
        image
      );
      
      // 存储纹理引用
      this.textures[texInfo.id] = texture;
      
      // 通知WebAssembly模块
      const nameString = this.wasmModule.memoryManager.createString(texInfo.id);
      this.wasmModule.exports.register_texture(nameString.ptr, texture);
      nameString.free();
    }
  }
  
  // 更新相机
  updateCamera(cameraData) {
    const { position, target, up, fov, aspect, near, far } = cameraData;
    
    this.wasmModule.exports.update_camera(
      position[0], position[1], position[2],
      target[0], target[1], target[2],
      up[0], up[1], up[2],
      fov, aspect, near, far
    );
  }
  
  // 渲染一帧
  render(deltaTime) {
    // 清除画布
    this.gl.clearColor(0.0, 0.0, 0.0, 1.0);
    this.gl.clear(this.gl.COLOR_BUFFER_BIT | this.gl.DEPTH_BUFFER_BIT);
    
    // 调用WebAssembly渲染函数
    this.wasmModule.exports.render_frame(deltaTime);
  }
  
  // 创建WebGL着色器
  _createShader(type, source) {
    const shader = this.gl.createShader(
      type === 'vertex' ? this.gl.VERTEX_SHADER : this.gl.FRAGMENT_SHADER
    );
    
    this.gl.shaderSource(shader, source);
    this.gl.compileShader(shader);
    
    if (!this.gl.getShaderParameter(shader, this.gl.COMPILE_STATUS)) {
      const error = this.gl.getShaderInfoLog(shader);
      this.gl.deleteShader(shader);
      throw new Error(`Failed to compile ${type} shader: ${error}`);
    }
    
    return shader;
  }
  
  // 创建WebGL程序
  _createProgram(vertexShader, fragmentShader) {
    const program = this.gl.createProgram();
    
    this.gl.attachShader(program, vertexShader);
    this.gl.attachShader
```javascript
(program, fragmentShader);
    this.gl.linkProgram(program);
    
    if (!this.gl.getProgramParameter(program, this.gl.LINK_STATUS)) {
      const error = this.gl.getProgramInfoLog(program);
      this.gl.deleteProgram(program);
      throw new Error(`Failed to link shader program: ${error}`);
    }
    
    return program;
  }
  
  // 设置属性
  _setupAttributes() {
    // 获取属性位置
    this.attributes = {
      position: this.gl.getAttribLocation(this.program, 'a_position'),
      texCoord: this.gl.getAttribLocation(this.program, 'a_texCoord'),
      normal: this.gl.getAttribLocation(this.program, 'a_normal')
    };
  }
  
  // 设置Uniform
  _setupUniforms() {
    // 获取uniform位置
    this.uniforms = {
      modelViewMatrix: this.gl.getUniformLocation(this.program, 'u_modelViewMatrix'),
      projectionMatrix: this.gl.getUniformLocation(this.program, 'u_projectionMatrix'),
      normalMatrix: this.gl.getUniformLocation(this.program, 'u_normalMatrix'),
      sampler: this.gl.getUniformLocation(this.program, 'u_sampler')
    };
  }
  
  // 加载图像
  _loadImage(url) {
    return new Promise((resolve, reject) => {
      const image = new Image();
      image.onload = () => resolve(image);
      image.onerror = () => reject(new Error(`Failed to load image: ${url}`));
      image.src = url;
    });
  }
}

// 7. WASM组件架构 - 使用Web Assembly Components模型

class WasmComponentSystem {
  constructor() {
    this.components = new Map();
    this.interfaces = new Map();
  }
  
  async initialize() {
    // 配置WASM组件接口
    await this._initializeInterfaces();
    
    // 加载核心组件
    await this._loadCoreComponents();
    
    return this;
  }
  
  // 初始化接口定义
  async _initializeInterfaces() {
    // 这是WebAssembly Component Model的概念示例
    // 当前WebAssembly规范尚未完全实现此功能
    
    // 定义日志接口
    this.interfaces.set('logging', {
      methods: {
        log: {
          parameters: ['string'],
          results: []
        },
        error: {
          parameters: ['string'],
          results: []
        }
      }
    });
    
    // 定义存储接口
    this.interfaces.set('storage', {
      methods: {
        get: {
          parameters: ['string'],
          results: ['option<string>']
        },
        set: {
          parameters: ['string', 'string'],
          results: ['bool']
        },
        remove: {
          parameters: ['string'],
          results: ['bool']
        }
      }
    });
    
    // 定义HTTP接口
    this.interfaces.set('http', {
      methods: {
        fetch: {
          parameters: ['string', 'map<string,string>'],
          results: ['promise<httpResponse>']
        }
      },
      types: {
        httpResponse: {
          record: {
            status: 'u16',
            headers: 'map<string,string>',
            body: 'option<bytes>'
          }
        }
      }
    });
  }
  
  // 加载核心组件
  async _loadCoreComponents() {
    // 实现日志功能
    const loggingImpl = {
      log: (message) => console.log(`[WASM] ${message}`),
      error: (message) => console.error(`[WASM] ${message}`)
    };
    
    // 实现存储功能
    const storageImpl = {
      get: (key) => {
        const value = localStorage.getItem(key);
        return value !== null ? value : null;
      },
      set: (key, value) => {
        localStorage.setItem(key, value);
        return true;
      },
      remove: (key) => {
        localStorage.removeItem(key);
        return true;
      }
    };
    
    // 实现HTTP功能
    const httpImpl = {
      fetch: async (url, headers) => {
        try {
          const response = await fetch(url, { headers });
          
          const responseHeaders = {};
          response.headers.forEach((value, key) => {
            responseHeaders[key] = value;
          });
          
          const body = await response.arrayBuffer();
          
          return {
            status: response.status,
            headers: responseHeaders,
            body: body
          };
        } catch (error) {
          console.error('HTTP fetch error:', error);
          return {
            status: 0,
            headers: {},
            body: null
          };
        }
      }
    };
    
    // 注册核心实现
    this._registerImplementation('logging', loggingImpl);
    this._registerImplementation('storage', storageImpl);
    this._registerImplementation('http', httpImpl);
  }
  
  // 注册接口实现
  _registerImplementation(interfaceName, implementation) {
    if (!this.interfaces.has(interfaceName)) {
      throw new Error(`Interface '${interfaceName}' not defined`);
    }
    
    // 存储实现
    this.components.set(interfaceName, {
      interface: this.interfaces.get(interfaceName),
      implementation
    });
    
    console.log(`Registered implementation for '${interfaceName}' interface`);
  }
  
  // 加载WASM组件
  async loadComponent(name, url) {
    try {
      // 获取.wasm文件
      const response = await fetch(url);
      
      if (!response.ok) {
        throw new Error(`Failed to fetch component: ${url}`);
      }
      
      const bytes = await response.arrayBuffer();
      
      // 这里是一个简化版的组件加载过程
      // 未来的WebAssembly Component Model将提供更标准化的API
      
      // 创建导入对象，包含所有已注册的接口实现
      const imports = {};
      
      for (const [interfaceName, component] of this.components.entries()) {
        imports[interfaceName] = component.implementation;
      }
      
      // 编译和实例化模块
      const module = await WebAssembly.compile(bytes);
      const instance = await WebAssembly.instantiate(module, imports);
      
      // 注册组件
      this.components.set(name, {
        interface: null, // 组件可能实现多个接口
        implementation: instance.exports,
        module,
        instance
      });
      
      console.log(`Component '${name}' loaded successfully`);
      
      return instance.exports;
    } catch (error) {
      console.error(`Failed to load component '${name}':`, error);
      throw error;
    }
  }
  
  // 调用组件方法
  callComponent(componentName, methodName, ...args) {
    const component = this.components.get(componentName);
    
    if (!component) {
      throw new Error(`Component '${componentName}' not found`);
    }
    
    const method = component.implementation[methodName];
    
    if (typeof method !== 'function') {
      throw new Error(`Method '${methodName}' not found in component '${componentName}'`);
    }
    
    return method(...args);
  }
}

// 8. 使用实例 - 实际应用示例

// 主应用代码
async function initializeApplication() {
  try {
    console.log('Initializing WebAssembly application...');
    
    // 初始化图像处理器
    const imageProcessor = new ImageProcessor();
    await imageProcessor.initialize();
    
    // 设置UI事件
    document.getElementById('process-button').addEventListener('click', async () => {
      const imageInput = document.getElementById('image-input');
      const canvas = document.getElementById('output-canvas');
      const ctx = canvas.getContext('2d');
      
      if (imageInput.files.length === 0) {
        alert('Please select an image first');
        return;
      }
      
      // 读取选择的图像
      const file = imageInput.files[0];
      const image = await loadImageFromFile(file);
      
      // 调整画布大小
      canvas.width = image.width;
      canvas.height = image.height;
      
      // 将图像绘制到画布
      ctx.drawImage(image, 0, 0);
      
      // 获取图像数据
      const imageData = ctx.getImageData(0, 0, canvas.width, canvas.height);
      
      // 获取选择的处理操作
      const operations = getSelectedOperations();
      
      // 处理图像
      console.time('Image processing');
      const processedImageData = await imageProcessor.processImage(imageData, operations);
      console.timeEnd('Image processing');
      
      // 显示处理后的图像
      ctx.putImageData(processedImageData, 0, 0);
      
      // 更新UI
      document.getElementById('processing-status').textContent = 'Processing complete!';
    });
    
    // 初始化渲染器（如果需要）
    if (document.getElementById('3d-canvas')) {
      const renderer = new WasmWebGLRenderer();
      await renderer.initialize(document.getElementById('3d-canvas'));
      
      // 设置场景
      const sceneData = {
        vertices: [
          // 立方体顶点...
          -1.0, -1.0,  1.0,  0.0, 0.0,  0.0, 0.0, 1.0,
           1.0, -1.0,  1.0,  1.0, 0.0,  0.0, 0.0, 1.0,
           1.0,  1.0,  1.0,  1.0, 1.0,  0.0, 0.0, 1.0,
          -1.0,  1.0,  1.0,  0.0, 1.0,  0.0, 0.0, 1.0,
          
          -1.0, -1.0, -1.0,  1.0, 0.0,  0.0, 0.0, -1.0,
           1.0, -1.0, -1.0,  0.0, 0.0,  0.0, 0.0, -1.0,
           1.0,  1.0, -1.0,  0.0, 1.0,  0.0, 0.0, -1.0,
          -1.0,  1.0, -1.0,  1.0, 1.0,  0.0, 0.0, -1.0,
          
          // 更多面...
        ],
        indices: [
          // 立方体索引...
          0, 1, 2, 0, 2, 3, // 前面
          4, 5, 6, 4, 6, 7, // 后面
          // 更多面...
        ],
        textures: [
          { id: 'cube-texture', url: '/assets/textures/cube.jpg' }
        ]
      };
      
      renderer.setupScene(sceneData);
      
      // 设置相机
      renderer.updateCamera({
        position: [0, 0, 5],
        target: [0, 0, 0],
        up: [0, 1, 0],
        fov: 45,
        aspect: canvas.width / canvas.height,
        near: 0.1,
        far: 100
      });
      
      // 设置动画循环
      let lastTime = 0;
      
      function animate(time) {
        const deltaTime = lastTime ? (time - lastTime) / 1000 : 0;
        lastTime = time;
        
        renderer.render(deltaTime);
        requestAnimationFrame(animate);
      }
      
      requestAnimationFrame(animate);
    }
    
    // 初始化WASM组件系统（如果需要）
    const componentSystem = new WasmComponentSystem();
    await componentSystem.initialize();
    
    // 加载自定义组件
    const dataProcessor = await componentSystem.loadComponent(
      'data-processor', 
      '/wasm/data_processor.wasm'
    );
    
    // 使用组件
    document.getElementById('process-data-button')?.addEventListener('click', async () => {
      const inputData = document.getElementById('data-input').value;
      
      // 调用WASM组件处理数据
      const result = componentSystem.callComponent(
        'data-processor', 
        'processData', 
        inputData
      );
      
      document.getElementById('data-output').textContent = result;
    });
    
    console.log('WebAssembly application initialized successfully');
  } catch (error) {
    console.error('Failed to initialize application:', error);
    document.getElementById('error-message').textContent = 
      `Failed to initialize: ${error.message}`;
  }
}

// 辅助函数
function loadImageFromFile(file) {
  return new Promise((resolve, reject) => {
    const reader = new FileReader();
    
    reader.onload = (e) => {
      const image = new Image();
      image.onload = () => resolve(image);
      image.onerror = () => reject(new Error('Failed to load image'));
      image.src = e.target.result;
    };
    
    reader.onerror = () => reject(new Error('Failed to read file'));
    reader.readAsDataURL(file);
  });
}

function getSelectedOperations() {
  const operations = [];
  
  // 检查各个处理选项
  if (document.getElementById('grayscale-checkbox').checked) {
    operations.push({ type: 'filter', name: 'grayscale' });
  }
  
  if (document.getElementById('blur-checkbox').checked) {
    const radius = parseFloat(document.getElementById('blur-radius').value) || 3;
    operations.push({ type: 'filter', name: 'blur', params: { radius } });
  }
  
  if (document.getElementById('brightness-checkbox').checked) {
    const factor = parseFloat(document.getElementById('brightness-factor').value) || 1.0;
    operations.push({ type: 'filter', name: 'brightness', params: { factor } });
  }
  
  if (document.getElementById('rotate-checkbox').checked) {
    const angle = parseFloat(document.getElementById('rotation-angle').value) || 0;
    operations.push({ type: 'transform', name: 'rotate', params: { angle } });
  }
  
  return operations;
}

// 初始化应用
document.addEventListener('DOMContentLoaded', initializeApplication);
```

**WebAssembly架构特点**：

- 接近原生的性能表现
- 与JavaScript高效互操作
- 内存管理与生命周期控制
- 多线程并行处理能力
- 与WebGL集成实现高性能渲染
- 模块化组件设计促进代码复用
- 跨语言编译支持多种源语言

### 7.3 边缘计算模式

-**边缘计算架构**

```javascript
// 边缘计算架构示例

// 1. 边缘服务器 - CloudFlare Workers示例

// main.js - CloudFlare Worker入口点
addEventListener('fetch', event => {
  event.respondWith(handleRequest(event));
});

async function handleRequest(event) {
  const request = event.request;
  const url = new URL(request.url);
  const cache = caches.default;
  
  // 简单的路由系统
  try {
    // 优先检查缓存
    let cachedResponse = await cache.match(request);
    if (cachedResponse) {
      // 添加缓存命中标头
      cachedResponse = new Response(cachedResponse.body, cachedResponse);
      cachedResponse.headers.set('X-Edge-Cache', 'HIT');
      return cachedResponse;
    }

    // 处理API请求
    if (url.pathname.startsWith('/api/')) {
      return await handleApiRequest(request, url, event);
    }
    
    // 处理静态资源
    if (url.pathname.match(/\.(js|css|png|jpg|jpeg|gif|svg|woff2?)$/)) {
      return await handleAssetRequest(request, cache);
    }
    
    // 处理主页或其他HTML请求
    return await handlePageRequest(request, url, event);
  } catch (error) {
    console.error(`Edge error: ${error.message}`);
    return new Response(`Edge error: ${error.message}`, { status: 500 });
  }
}

async function handleApiRequest(request, url, event) {
  // 解析API路径
  const apiPath = url.pathname.replace('/api/', '');
  const segments = apiPath.split('/');
  
  // API路由处理
  switch (segments[0]) {
    case 'products':
      if (segments.length === 1) {
        // 获取产品列表
        return await getProducts(request, url);
      } else if (segments.length === 2) {
        // 获取单个产品
        return await getProduct(segments[1], request);
      }
      break;
    
    case 'cart':
      if (request.method === 'POST') {
        // 添加到购物车
        return await addToCart(request);
      } else if (request.method === 'GET') {
        // 获取购物车
        return await getCart(request);
      }
      break;
    
    case 'geo':
      // 地理位置基于内容个性化
      return handleGeoRequest(request);
      
    case 'auth':
      // 身份验证API
      return await handleAuthRequest(request, segments);
      
    default:
      return new Response('API not found', { status: 404 });
  }
  
  return new Response('API method not supported', { status: 405 });
}

async function handleAssetRequest(request, cache) {
  const assetResponse = await fetch(request);
  
  if (assetResponse.ok) {
    // 创建可变缓存响应
    const response = new Response(assetResponse.body, assetResponse);
    
    // 设置Cache-Control头，最大缓存时间30天
    response.headers.set('Cache-Control', 'public, max-age=2592000');
    
    // 将资源放入缓存
    event.waitUntil(cache.put(request, response.clone()));
    
    return response;
  }
  
  return assetResponse;
}

async function handlePageRequest(request, url, event) {
  // 获取用户位置
  const userLocation = request.cf ? request.cf.country : null;
  
  // 获取用户语言首选项
  const acceptLanguage = request.headers.get('Accept-Language') || 'en';
  const preferredLanguage = acceptLanguage.split(',')[0].trim().split('-')[0];
  
  // 从KV存储获取HTML模板
  const template = await TEMPLATES.get('main-template');
  
  if (!template) {
    return new Response('Template not found', { status: 500 });
  }
  
  // 获取内容
  const content = await getPageContent(url.pathname, preferredLanguage, userLocation);
  
  // 将内容注入模板
  const html = injectContent(template, content, {
    language: preferredLanguage,
    location: userLocation,
    url: url.toString()
  });
  
  // 创建响应
  const response = new Response(html, {
    headers: {
      'Content-Type': 'text/html; charset=UTF-8',
      'Cache-Control': 'public, max-age=3600'
    }
  });
  
  // 存储到缓存
  event.waitUntil(cache.put(request, response.clone()));
  
  return response;
}

async function getProducts(request, url) {
  // 从URL获取查询参数
  const category = url.searchParams.get('category');
  const page = parseInt(url.searchParams.get('page') || '1');
  const limit = parseInt(url.searchParams.get('limit') || '20');
  
  // 从KV存储获取产品数据
  let products = await PRODUCTS.get('all-products', 'json');
  
  if (!products) {
    // 回退到源API
    const productApiResponse = await fetch(`${ORIGIN_API}/products`);
    products = await productApiResponse.json();
    
    // 存储到KV以供将来使用
    await PRODUCTS.put('all-products', JSON.stringify(products), {
      expirationTtl: 3600 // 1小时过期
    });
  }
  
  // 过滤和分页
  if (category) {
    products = products.filter(p => p.category === category);
  }
  
  const total = products.length;
  const paginatedProducts = products.slice((page - 1) * limit, page * limit);
  
  return new Response(JSON.stringify({
    products: paginatedProducts,
    meta: {
      total,
      page,
      limit,
      pages: Math.ceil(total / limit)
    }
  }), {
    headers: {
      'Content-Type': 'application/json',
      'Cache-Control': 'public, max-age=60' // 1分钟缓存
    }
  });
}

async function getProduct(id, request) {
  // 从KV存储获取产品
  let product = await PRODUCTS.get(`product:${id}`, 'json');
  
  if (!product) {
    // 回退到源API
    const productApiResponse = await fetch(`${ORIGIN_API}/products/${id}`);
    
    if (!productApiResponse.ok) {
      return new Response('Product not found', { status: 404 });
    }
    
    product = await productApiResponse.json();
    
    // 存储到KV
    await PRODUCTS.put(`product:${id}`, JSON.stringify(product), {
      expirationTtl: 3600 // 1小时过期
    });
  }
  
  return new Response(JSON.stringify(product), {
    headers: {
      'Content-Type': 'application/json',
      'Cache-Control': 'public, max-age=300' // 5分钟缓存
    }
  });
}

async function handleGeoRequest(request) {
  // 从CF请求对象获取地理信息
  const geo = {
    country: request.cf?.country || 'Unknown',
    region: request.cf?.region || 'Unknown',
    city: request.cf?.city || 'Unknown',
    latitude: request.cf?.latitude || 0,
    longitude: request.cf?.longitude || 0,
    timezone: request.cf?.timezone || 'UTC'
  };
  
  return new Response(JSON.stringify(geo), {
    headers: {
      'Content-Type': 'application/json'
    }
  });
}

async function handleAuthRequest(request, segments) {
  if (segments[1] === 'login' && request.method === 'POST') {
    try {
      // 解析登录请求
      const { username, password } = await request.json();
      
      // 验证凭据
      const authResponse = await fetch(`${AUTH_SERVICE}/validate`, {
        method: 'POST',
        headers: {
          'Content-Type': 'application/json'
        },
        body: JSON.stringify({ username, password })
      });
      
      if (!authResponse.ok) {
        return new Response('Invalid credentials', { status: 401 });
      }
      
      const authData = await authResponse.json();
      
      // 创建JWT令牌
      const token = await generateToken(authData);
      
      return new Response(JSON.stringify({ token }), {
        headers: {
          'Content-Type': 'application/json'
        }
      });
    } catch (error) {
      return new Response(`Authentication error: ${error.message}`, { status: 500 });
    }
  } else if (segments[1] === 'verify' && request.method === 'GET') {
    try {
      // 验证令牌
      const authHeader = request.headers.get('Authorization') || '';
      const token = authHeader.replace('Bearer ', '');
      
      if (!token) {
        return new Response('Missing token', { status: 401 });
      }
      
      // 验证令牌
      const payload = await verifyToken(token);
      
      return new Response(JSON.stringify({ valid: true, user: payload.user }), {
        headers: {
          'Content-Type': 'application/json'
        }
      });
    } catch (error) {
      return new Response(JSON.stringify({ valid: false, error: error.message }), {
        status: 401,
        headers: {
          'Content-Type': 'application/json'
        }
      });
    }
  }
  
  return new Response('Auth method not supported', { status: 405 });
}

// 辅助函数
async function generateToken(authData) {
  // 使用Web Crypto API创建令牌
  // 实际实现可能会更复杂
  const header = {
    alg: 'HS256',
    typ: 'JWT'
  };
  
  const payload = {
    sub: authData.userId,
    user: {
      id: authData.userId,
      name: authData.name,
      role: authData.role
    },
    exp: Math.floor(Date.now() / 1000) + 3600 // 1小时过期
  };
  
  const encodedHeader = btoa(JSON.stringify(header));
  const encodedPayload = btoa(JSON.stringify(payload));
  
  const key = await crypto.subtle.importKey(
    'raw',
    new TextEncoder().encode(JWT_SECRET),
    { name: 'HMAC', hash: 'SHA-256' },
    false,
    ['sign']
  );
  
  const signature = await crypto.subtle.sign(
    'HMAC',
    key,
    new TextEncoder().encode(`${encodedHeader}.${encodedPayload}`)
  );
  
  const encodedSignature = btoa(String.fromCharCode(...new Uint8Array(signature)));
  
  return `${encodedHeader}.${encodedPayload}.${encodedSignature}`;
}

async function verifyToken(token) {
  // 拆分令牌
  const [encodedHeader, encodedPayload, encodedSignature] = token.split('.');
  
  // 解码头部和载荷
  const header = JSON.parse(atob(encodedHeader));
  const payload = JSON.parse(atob(encodedPayload));
  
  // 检查过期时间
  if (payload.exp && payload.exp < Math.floor(Date.now() / 1000)) {
    throw new Error('Token expired');
  }
  
  // 验证签名
  const key = await crypto.subtle.importKey(
    'raw',
    new TextEncoder().encode(JWT_SECRET),
    { name: 'HMAC', hash: 'SHA-256' },
    false,
    ['verify']
  );
  
  const signature = new Uint8Array(
    atob(encodedSignature).split('').map(c => c.charCodeAt(0))
  );
  
  const valid = await crypto.subtle.verify(
    'HMAC',
    key,
    signature,
    new TextEncoder().encode(`${encodedHeader}.${encodedPayload}`)
  );
  
  if (!valid) {
    throw new Error('Invalid signature');
  }
  
  return payload;
}

// 2. 边缘函数 - AWS Lambda@Edge示例

// lambda-at-edge.js - Lambda@Edge视图器请求处理器
exports.handler = async (event) => {
  const request = event.Records[0].cf.request;
  const headers = request.headers;
  const uri = request.uri;
  
  // URI重写规则
  if (uri.endsWith('/') || !uri.includes('.')) {
    // 将请求重定向到索引页面
    request.uri = uri.replace(/\/$/, '') + '/index.html';
  }
  
  // 语言重定向
  const acceptLanguage = headers['accept-language'];
  if (acceptLanguage && uri === '/index.html') {
    const language = acceptLanguage[0].value.split(',')[0].trim().split('-')[0];
    
    // 重定向到语言特定页面
    if (language === 'fr') {
      request.uri = '/fr/index.html';
    } else if (language === 'de') {
      request.uri = '/de/index.html';
    } else if (language === 'es') {
      request.uri = '/es/index.html';
    }
  }
  
  // 添加安全头部
  if (uri.endsWith('.html')) {
    request.headers['x-forwarded-host'] = [{
      key: 'X-Forwarded-Host',
      value: headers['host'][0].value
    }];
  }
  
  return request;
};

// lambda-at-edge-response.js - Lambda@Edge视图器响应处理器
exports.handler = async (event) => {
  const response = event.Records[0].cf.response;
  const request = event.Records[0].cf.request;
  const headers = response.headers;
  
  // 添加安全头部
  headers['strict-transport-security'] = [{
    key: 'Strict-Transport-Security',
    value: 'max-age=63072000; includeSubdomains; preload'
  }];
  
  headers['content-security-policy'] = [{
    key: 'Content-Security-Policy',
    value: "default-src '
        },
        body: JSON.stringify({ username, password })
      });
      
      if (!authResponse.ok) {
        throw new Error('Invalid credentials');
      }
      
      const { token, user } = await authResponse.json();
      
      // 创建带有JWT的响应
      return new Response(
        JSON.stringify({ token, user }), 
        { 
          headers: { 'Content-Type': 'application/json' },
          status: 200
        }
      );
    } catch (error) {
      return new Response(
        JSON.stringify({ error: error.message }), 
        {
          headers: { 'Content-Type': 'application/json' },
          status: 401
        }
      );
    }
  }
  
  return new Response('Auth endpoint not found', { status: 404 });
}

// 2. 边缘设备应用 - IoT设备示例

// config.js - 配置文件
module.exports = {
  // 设备配置
  device: {
    id: process.env.DEVICE_ID || 'device-001',
    name: process.env.DEVICE_NAME || 'Smart Gateway',
    type: 'gateway'
  },
  
  // 网络配置
  network: {
    wifi: {
      ssid: process.env.WIFI_SSID,
      password: process.env.WIFI_PASSWORD
    },
    mqtt: {
      broker: process.env.MQTT_BROKER || 'mqtt://broker.hivemq.com',
      username: process.env.MQTT_USERNAME,
      password: process.env.MQTT_PASSWORD,
      clientId: process.env.MQTT_CLIENT_ID || `gateway-${Math.random().toString(16).substr(2, 8)}`
    },
    api: {
      endpoint: process.env.API_ENDPOINT || 'https://api.example.com/iot',
      apiKey: process.env.API_KEY
    }
  },
  
  // 传感器配置
  sensors: [
    {
      id: 'temp-001',
      type: 'temperature',
      pin: 4,
      interval: 60000, // 每分钟读取一次
      thresholds: {
        low: 10,
        high: 35
      }
    },
    {
      id: 'humidity-001',
      type: 'humidity',
      pin: 5,
      interval: 60000,
      thresholds: {
        low: 30,
        high: 80
      }
    },
    {
      id: 'motion-001',
      type: 'motion',
      pin: 6,
      mode: 'event' // 事件驱动而非轮询
    }
  ],
  
  // 边缘处理配置
  edge: {
    enableLocalProcessing: true,
    enableLocalStorage: true,
    localDbPath: './data/local.db',
    syncInterval: 300000, // 5分钟同步一次
    offlineMode: {
      enabled: true,
      maxStorageSize: 100 * 1024 * 1024 // 100MB
    }
  },
  
  // 更新配置
  updates: {
    checkInterval: 86400000, // 每天检查一次
    autoInstall: true
  }
};

// app.js - 边缘设备主应用
const config = require('./config');
const mqtt = require('mqtt');
const fs = require('fs');
const path = require('path');
const { Database } = require('sqlite3');
const { SensorManager } = require('./sensors');
const { RuleEngine } = require('./rules');
const { DeviceManager } = require('./devices');
const { LocalApi } = require('./local-api');

class EdgeGateway {
  constructor() {
    this.config = config;
    this.isConnected = false;
    this.isPending = false;
    this.lastSyncTime = 0;
    this.bootTime = Date.now();
    
    // 初始化本地存储
    this.initStorage();
    
    // 初始化传感器管理
    this.sensorManager = new SensorManager(config.sensors);
    
    // 初始化设备管理
    this.deviceManager = new DeviceManager();
    
    // 初始化规则引擎
    this.ruleEngine = new RuleEngine();
    
    // 初始化本地API
    this.localApi = new LocalApi(this);
    
    // 加载持久化规则
    this.loadRules();
  }
  
  async start() {
    console.log(`Starting edge gateway ${this.config.device.id}...`);
    
    // 连接MQTT代理
    await this.connectMqtt();
    
    // 初始化传感器
    await this.sensorManager.initialize();
    
    // 发现本地设备
    await this.deviceManager.discoverDevices();
    
    // 启动本地API服务
    await this.localApi.start();
    
    // 发送在线状态
    this.publishStatus('online');
    
    // 设置同步定时器
    this.setupSyncTimer();
    
    // 设置传感器事件监听
    this.sensorManager.on('reading', this.handleSensorReading.bind(this));
    this.sensorManager.on('alert', this.handleSensorAlert.bind(this));
    
    // 设置设备事件监听
    this.deviceManager.on('deviceConnected', this.handleDeviceConnected.bind(this));
    this.deviceManager.on('deviceDisconnected', this.handleDeviceDisconnected.bind(this));
    this.deviceManager.on('deviceData', this.handleDeviceData.bind(this));
    
    console.log('Edge gateway started successfully');
  }
  
  async connectMqtt() {
    return new Promise((resolve, reject) => {
      try {
        const { broker, username, password, clientId } = this.config.network.mqtt;
        
        // 连接选项
        const options = {
          clientId,
          clean: true,
          connectTimeout: 5000,
          reconnectPeriod: 5000
        };
        
        // 如果提供了凭据则使用
        if (username && password) {
          options.username = username;
          options.password = password;
        }
        
        // 连接MQTT代理
        this.mqttClient = mqtt.connect(broker, options);
        
        // 注册事件处理程序
        this.mqttClient.on('connect', () => {
          console.log(`Connected to MQTT broker at ${broker}`);
          this.isConnected = true;
          
          // 订阅主题
          this.mqttClient.subscribe(`devices/${this.config.device.id}/commands/#`);
          this.mqttClient.subscribe('broadcast/#');
          
          resolve();
        });
        
        this.mqttClient.on('message', this.handleMqttMessage.bind(this));
        
        this.mqttClient.on('error', (error) => {
          console.error(`MQTT error: ${error.message}`);
          this.isConnected = false;
        });
        
        this.mqttClient.on('offline', () => {
          console.log('MQTT client went offline');
          this.isConnected = false;
          
          // 进入离线模式
          if (this.config.edge.offlineMode.enabled) {
            this.enterOfflineMode();
          }
        });
      } catch (error) {
        console.error(`Failed to connect to MQTT: ${error.message}`);
        reject(error);
      }
    });
  }
  
  // 处理MQTT消息
  handleMqttMessage(topic, message) {
    try {
      const payload = JSON.parse(message.toString());
      console.log(`Received message on topic ${topic}: ${JSON.stringify(payload)}`);
      
      // 指令处理
      if (topic.startsWith(`devices/${this.config.device.id}/commands/`)) {
        const command = topic.split('/').pop();
        this.handleCommand(command, payload);
      }
      
      // 广播消息处理
      if (topic.startsWith('broadcast/')) {
        const broadcastType = topic.split('/').pop();
        this.handleBroadcast(broadcastType, payload);
      }
    } catch (error) {
      console.error(`Error handling MQTT message: ${error.message}`);
    }
  }
  
  // 处理传感器读数
  handleSensorReading(sensorId, reading) {
    console.log(`Sensor ${sensorId} reading: ${JSON.stringify(reading)}`);
    
    // 本地存储读数
    this.storeReading(sensorId, reading);
    
    // 应用规则引擎
    this.ruleEngine.evaluateRules('sensorReading', {
      sensorId,
      reading,
      gateway: this.config.device.id,
      timestamp: Date.now()
    });
    
    // 发布到MQTT，如果已连接
    if (this.isConnected) {
      this.mqttClient.publish(
        `devices/${this.config.device.id}/sensors/${sensorId}`,
        JSON.stringify({
          timestamp: Date.now(),
          reading
        })
      );
    }
  }
  
  // 处理传感器告警
  handleSensorAlert(sensorId, alert) {
    console.log(`Sensor ${sensorId} alert: ${JSON.stringify(alert)}`);
    
    // 存储告警
    this.storeAlert(sensorId, alert);
    
    // 应用规则引擎
    this.ruleEngine.evaluateRules('sensorAlert', {
      sensorId,
      alert,
      gateway: this.config.device.id,
      timestamp: Date.now()
    });
    
    // 高优先级：即使离线也尝试发送
    this.publishAlert(sensorId, alert);
  }
  
  // 发布告警
  publishAlert(sensorId, alert) {
    const alertTopic = `devices/${this.config.device.id}/alerts`;
    const alertPayload = {
      sensorId,
      alert,
      timestamp: Date.now(),
      deviceId: this.config.device.id
    };
    
    // 如果连接到MQTT，直接发布
    if (this.isConnected) {
      this.mqttClient.publish(alertTopic, JSON.stringify(alertPayload), { qos: 1 });
      return;
    }
    
    // 否则，尝试通过HTTP API发送
    fetch(`${this.config.network.api.endpoint}/alerts`, {
      method: 'POST',
      headers: {
        'Content-Type': 'application/json',
        'X-API-Key': this.config.network.api.apiKey
      },
      body: JSON.stringify(alertPayload)
    }).catch(error => {
      console.error(`Failed to send alert via API: ${error.message}`);
      
      // 存入待发送队列
      this.storePendingMessage(alertTopic, alertPayload);
    });
  }
  
  // 同步数据到云端
  async syncData() {
    if (!this.isConnected || this.isPending) {
      return;
    }
    
    try {
      this.isPending = true;
      console.log('Starting data synchronization with cloud...');
      
      // 获取自上次同步以来的读数
      const newReadings = await this.getReadingsSinceLastSync();
      
      if (newReadings.length > 0) {
        console.log(`Syncing ${newReadings.length} new readings...`);
        
        // 批量发布读数
        this.mqttClient.publish(
          `devices/${this.config.device.id}/batch-readings`,
          JSON.stringify({
            readings: newReadings,
            timestamp: Date.now()
          }),
          { qos: 1 }
        );
      }
      
      // 发送所有待发送的消息
      await this.sendPendingMessages();
      
      // 更新同步时间
      this.lastSyncTime = Date.now();
      console.log('Data synchronization completed');
    } catch (error) {
      console.error(`Sync error: ${error.message}`);
    } finally {
      this.isPending = false;
    }
  }
  
  // 初始化存储
  initStorage() {
    const dbPath = this.config.edge.localDbPath;
    const dbDir = path.dirname(dbPath);
    
    // 确保目录存在
    if (!fs.existsSync(dbDir)) {
      fs.mkdirSync(dbDir, { recursive: true });
    }
    
    // 打开数据库
    this.db = new Database(dbPath, (err) => {
      if (err) {
        console.error(`Failed to open database: ${err.message}`);
        return;
      }
      
      // 创建表
      this.db.exec(`
        CREATE TABLE IF NOT EXISTS readings (
          id INTEGER PRIMARY KEY AUTOINCREMENT,
          sensor_id TEXT NOT NULL,
          timestamp INTEGER NOT NULL,
          value REAL NOT NULL,
          type TEXT NOT NULL,
          synced INTEGER DEFAULT 0
        );
        
        CREATE TABLE IF NOT EXISTS alerts (
          id INTEGER PRIMARY KEY AUTOINCREMENT,
          sensor_id TEXT NOT NULL,
          timestamp INTEGER NOT NULL,
          type TEXT NOT NULL,
          message TEXT NOT NULL,
          level TEXT NOT NULL,
          synced INTEGER DEFAULT 0
        );
        
        CREATE TABLE IF NOT EXISTS pending_messages (
          id INTEGER PRIMARY KEY AUTOINCREMENT,
          topic TEXT NOT NULL,
          payload TEXT NOT NULL,
          timestamp INTEGER NOT NULL,
          attempts INTEGER DEFAULT 0
        );
        
        CREATE TABLE IF NOT EXISTS rules (
          id INTEGER PRIMARY KEY AUTOINCREMENT,
          name TEXT NOT NULL,
          condition TEXT NOT NULL,
          actions TEXT NOT NULL,
          enabled INTEGER DEFAULT 1
        );
      `);
    });
  }
  
  // 存储传感器读数
  storeReading(sensorId, reading) {
    if (!this.db) return;
    
    const stmt = this.db.prepare(`
      INSERT INTO readings (sensor_id, timestamp, value, type, synced)
      VALUES (?, ?, ?, ?, ?)
    `);
    
    stmt.run(
      sensorId,
      Date.now(),
      reading.value,
      reading.type,
      this.isConnected ? 1 : 0
    );
    
    stmt.finalize();
  }
  
  // 获取自上次同步以来的读数
  getReadingsSinceLastSync() {
    return new Promise((resolve, reject) => {
      if (!this.db) {
        resolve([]);
        return;
      }
      
      this.db.all(
        `SELECT * FROM readings WHERE timestamp > ? AND synced = 0`,
        [this.lastSyncTime],
        (err, rows) => {
          if (err) {
            reject(err);
            return;
          }
          
          // 标记为已同步
          if (rows.length > 0) {
            const ids = rows.map(r => r.id).join(',');
            this.db.run(`UPDATE readings SET synced = 1 WHERE id IN (${ids})`);
          }
          
          resolve(rows);
        }
      );
    });
  }
  
  // 进入离线模式
  enterOfflineMode() {
    console.log('Entering offline mode...');
    
    // 确保本地处理已启用
    if (!this.config.edge.enableLocalProcessing) {
      console.warn('Local processing is disabled, limited functionality in offline mode');
    }
    
    // 增加传感器数据本地存储
    this.sensorManager.enableHighFrequencyLocalStorage();
    
    // 减少电源消耗
    this.sensorManager.adjustSamplingRatesForOffline();
    
    // 通知连接的设备
    this.deviceManager.broadcastOfflineMode();
  }
  
  // 退出离线模式
  exitOfflineMode() {
    console.log('Exiting offline mode...');
    
    // 恢复正常操作
    this.sensorManager.restoreDefaultSettings();
    
    // 立即同步数据
    this.syncData();
    
    // 通知连接的设备
    this.deviceManager.broadcastOnlineMode();
  }
  
  // 设置同步计时器
  setupSyncTimer() {
    setInterval(() => {
      if (this.isConnected) {
        this.syncData();
      }
    }, this.config.edge.syncInterval);
  }
  
  // 发布设备状态
  publishStatus(status) {
    if (!this.isConnected) {
      return;
    }
    
    this.mqttClient.publish(
      `devices/${this.config.device.id}/status`,
      JSON.stringify({
        status,
        timestamp: Date.now(),
        uptime: Date.now() - this.bootTime,
        version: process.env.VERSION || '1.0.0',
        sensors: this.sensorManager.getSensorsStatus(),
        connectedDevices: this.deviceManager.getConnectedDevicesCount()
      }),
      { qos: 1, retain: true }
    );
  }
}

// 启动应用
const gateway = new EdgeGateway();
gateway.start().catch(error => {
  console.error(`Failed to start gateway: ${error.message}`);
  process.exit(1);
});

// 优雅地处理进程退出
process.on('SIGINT', async () => {
  console.log('Shutting down...');
  await gateway.publishStatus('offline');
  process.exit(0);
});

```

**边缘计算架构特点**：

- 分布式计算能力靠近数据源
- 降低延迟满足实时处理需求
- 离线模式支持网络连接中断
- 本地处理减少云传输带宽
- 设备间直接通信缩短响应时间
- 智能决策在边缘完成
- 分层架构实现数据分级处理

## 8. 软件架构思维导图

```text

现代软件架构全景
├── 前端架构
│   ├── UI框架
│   │   ├── React生态系统
│   │   │   ├── 虚拟DOM
│   │   │   ├── JSX
│   │   │   ├── 组件模型
│   │   │   └── Hooks
│   │   ├── Vue架构
│   │   │   ├── 响应式系统
│   │   │   ├── 单文件组件
│   │   │   ├── 指令系统
│   │   │   └── 组合式API
│   │   ├── Angular架构
│   │   │   ├── 依赖注入
│   │   │   ├── TypeScript支持
│   │   │   ├── RxJS集成
│   │   │   └── NgModules
│   │   └── Svelte
│   │       ├── 编译时框架
│   │       ├── 零运行时依赖
│   │       ├── 反应式声明
│   │       └── 作用域CSS
│   ├── 状态管理
│   │   ├── 集中式 (Redux)
│   │   ├── 响应式 (MobX)
│   │   ├── 原子化 (Recoil/Jotai)
│   │   └── 查询缓存 (React Query)
│   ├── 组件设计模式
│   │   ├── 组合模式
│   │   ├── 原子设计系统
│   │   ├── 状态机组件
│   │   └── 服务器组件
│   └── 构建/优化
│       ├── Vite/Webpack
│       ├── 代码分割
│       ├── Tree Shaking
│       ├── 懒加载
│       └── 性能优化
├── 后端架构
│   ├── 服务器框架
│   │   ├── Express (Node.js)
│   │   ├── NestJS (Node.js)
│   │   ├── Echo (Go)
│   │   ├── Spring Boot (Java)
│   │   └── Django (Python)
│   ├── API设计
│   │   ├── REST
│   │   ├── GraphQL
│   │   └── gRPC
│   ├── 应用架构
│   │   ├── 单体应用
│   │   ├── 微服务
│   │   └── 函数即服务 (FaaS)
│   └── 通信模式
│       ├── 同步通信
│       ├── 异步消息队列
│       ├── 发布/订阅
│       └── 事件流
├── 数据架构
│   ├── 数据库系统
│   │   ├── 关系型
│   │   │   ├── PostgreSQL
│   │   │   ├── MySQL/MariaDB
│   │   │   └── NewSQL (CockroachDB)
│   │   ├── NoSQL
│   │   │   ├── 文档型 (MongoDB)
│   │   │   ├── 键值型 (Redis)
│   │   │   ├── 列族型 (Cassandra)
│   │   │   └── 时序型 (InfluxDB)
│   │   └── 多模型数据库
│   ├── 数据访问
│   │   ├── ORM
│   │   ├── 数据映射器
│   │   └── 存储库模式
│   └── 缓存策略
│       ├── 多级缓存
│       ├── 缓存模式 (Cache-Aside等)
│       ├── 失效策略
│       └── 分布式缓存
├── 全栈架构模式
│   ├── JAMStack
│   │   ├── 静态站点生成
│   │   ├── 客户端API调用
│   │   └── 无服务器函数
│   ├── MERN/MEAN/PERN栈
│   │   ├── 前端框架
│   │   ├── API服务
│   │   └── 数据库集成
│   ├── 云原生应用
│   │   ├── 容器化
│   │   ├── Kubernetes
│   │   ├── 微服务配置
│   │   └── CI/CD管道
│   └── 服务网格
│       ├── 服务发现
│       ├── 负载均衡
│       ├── 流量管理
│       └── 可观测性
├── 热门开源应用架构
│   ├── VSCode
│   │   ├── 扩展API
│   │   ├── 语言服务协议
│   │   └── 工作区架构
│   ├── Next.js
│   │   ├── 渲染策略
│   │   ├── 数据获取
│   │   └── 路由系统
│   ├── Redis
│   │   ├── 事件循环
│   │   ├── 数据结构
│   │   └── 持久化策略
│   └── Kubernetes
│       ├── 控制平面
│       ├── 节点组件
│       ├── 资源模型
│       └── 扩展机制
└── 新兴架构趋势
    ├── AI驱动架构
    │   ├── LLM集成
    │   ├── 向量数据库
    │   ├── 语义路由
    │   └── 多代理系统
    ├── WebAssembly
    │   ├── 模块加载
    │   ├── 内存交互
    │   ├── 复杂应用设计
    │   └── Web/非Web环境
    └── 边缘计算
        ├── CDN边缘
        ├── IoT边缘
        ├── 数据处理模式
        └── 离线模式设计

```

## 9. 总结

现代软件架构已经发展成为一个复杂而多元的生态系统，融合了多种范式、技术栈和设计原则。
本文从前端到后端的全栈视角，系统性地分析了当今软件架构的多个方面：

1. **前端架构**

经历了从简单DOM操作到复杂应用平台的转变，React、Vue、Angular和Svelte等框架代表了不同的设计理念；
状态管理从集中式发展到原子化和查询为中心；
组件设计模式变得更加灵活和可组合；
构建优化工具链大幅提升了开发效率和运行性能。

1. **后端架构**

在多语言环境下呈现多样化，Express、NestJS、Echo等框架各具特色；
API设计范式包括REST、GraphQL和gRPC各有优势；
应用架构从单体走向微服务和函数即服务，追求更高的可扩展性和弹性。

1. **数据架构**

面临多样化的存储需求，关系型数据库持续创新，NoSQL解决方案针对特定场景提供优化；
数据访问模式从ORM到数据映射器再到存储库模式，平衡了抽象与性能；
多级缓存策略成为标准实践，解决了吞吐量和延迟挑战。

1. **全栈架构模式**

如JAMStack、MERN/MEAN/PERN栈和云原生应用，提供了端到端的方案组合；
服务网格简化了复杂分布式系统的管理，提供了更强的可靠性和可观测性。

1. **热门开源项目**

如VSCode、Next.js、Redis和Kubernetes，代表了各自领域的架构最佳实践，影响了整个行业的发展方向。

1. **新兴架构趋势**

包括AI驱动的软件架构、WebAssembly应用架构和边缘计算模式，正在重塑软件的设计和交付方式，开辟新的可能性。

在这个快速变化的环境中，软件架构师和开发者需要不断学习和适应，选择适合特定问题域的技术栈和模式，
平衡创新与稳定性，以构建出高效、可靠、可维护的现代软件系统。
未来的软件架构将更加智能化、分散化和用户友好，同时保持对可靠性、安全性和性能的关注。

随着技术的不断发展，这份分析也将需要持续更新，以反映软件架构领域的最新趋势和最佳实践。
愿这份文档能为你的架构决策提供有价值的参考。
