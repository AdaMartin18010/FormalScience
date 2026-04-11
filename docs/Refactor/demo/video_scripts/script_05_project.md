# 视频脚本：项目实战 (45分钟)

> **目标受众**: 想要完成完整项目的开发者
> **学习目标**: 从零开始构建一个经过形式化验证的应用

---

## 视频信息

| 项目 | 内容 |
|-----|------|
| 视频标题 | FormalScience 项目实战：构建验证过的待办事项应用 |
| 预计时长 | 45分钟 |
| 分辨率 | 1920x1080 |
| 配音语言 | 中文 |
| 项目难度 | 中级 |
| 先修要求 | 完成入门教程，了解基本验证概念 |

---

## 项目概述

### 项目目标

构建一个**经过形式化验证的待办事项管理应用**，包含：

- 完整的后端 API
- 数据持久化
- 基本的前端界面
- 关键功能的正确性验证

### 技术栈

```
后端: Python + FormalScience + Flask
前端: HTML + JavaScript (简单实现)
数据库: SQLite
验证: FormalScience Verifier
```

### 项目结构

```
todo_app/
├── src/
│   ├── __init__.py
│   ├── models.py       # 数据模型 + 验证
│   ├── storage.py      # 数据存储
│   ├── api.py          # REST API
│   └── app.py          # 应用入口
├── tests/
│   ├── test_models.py
│   ├── test_storage.py
│   └── test_api.py
├── static/
│   └── (前端文件)
├── templates/
│   └── index.html
├── verify/             # 验证规范
│   ├── todo_spec.py
│   └── invariants.py
├── requirements.txt
└── README.md
```

---

## 课程大纲

### 第1章：项目初始化 (0:00-5:00)

**目标**: 创建项目结构，配置开发环境

**内容**:

1. 项目需求分析
2. 创建目录结构
3. 初始化 Git 仓库
4. 安装依赖
5. 配置开发环境

**关键产出**:

- 完整的项目目录
- requirements.txt
- 开发环境就绪

---

### 第2章：数据模型设计 (5:00-15:00)

**目标**: 设计并验证数据模型

**内容**:

1. 定义 Todo 实体
2. 设计状态机
3. 编写数据验证规则
4. 形式化验证模型

**关键代码**:

```python
# src/models.py
from dataclasses import dataclass
from datetime import datetime
from enum import Enum, auto
from formal_science import invariant, requires, ensures

class TodoStatus(Enum):
    PENDING = auto()
    IN_PROGRESS = auto()
    COMPLETED = auto()
    CANCELLED = auto()

@dataclass
class Todo:
    """待办事项实体 - 带形式化验证"""

    id: int
    title: str
    description: str
    status: TodoStatus
    created_at: datetime
    updated_at: datetime
    due_date: datetime | None = None

    # 不变式：每个待办事项都有标题
    @invariant("len(self.title) > 0")
    # 不变式：创建时间 <= 更新时间
    @invariant("self.created_at <= self.updated_at")
    # 不变式：有效状态
    @invariant("self.status in TodoStatus")
    def __post_init__(self):
        self.validate()

    @requires("len(title) > 0", "标题不能为空")
    @requires("len(title) <= 200", "标题不能超过200字符")
    @ensures("self.title == title")
    @ensures("self.updated_at > old(self.updated_at)")
    def update_title(self, title: str):
        """更新标题"""
        self.title = title
        self.updated_at = datetime.now()

    @requires("self.status != TodoStatus.COMPLETED", "已完成事项不能重复完成")
    @ensures("self.status == TodoStatus.COMPLETED")
    @ensures("self.updated_at > old(self.updated_at)")
    def complete(self):
        """标记为完成"""
        self.status = TodoStatus.COMPLETED
        self.updated_at = datetime.now()

    @requires("self.status == TodoStatus.PENDING", "只能开始待处理的事项")
    @ensures("self.status == TodoStatus.IN_PROGRESS")
    def start(self):
        """开始处理"""
        self.status = TodoStatus.IN_PROGRESS
        self.updated_at = datetime.now()

    def validate(self):
        """验证实体状态"""
        assert len(self.title) > 0, "标题不能为空"
        assert self.created_at <= self.updated_at, "时间顺序错误"
        assert isinstance(self.status, TodoStatus), "无效状态"
```

**验证**:

```bash
formal-verify src/models.py --verbose
```

---

### 第3章：存储层实现 (15:00-25:00)

**目标**: 实现数据持久化层

**内容**:

1. 设计存储接口
2. 实现 SQLite 存储
3. 添加数据完整性约束
4. 验证存储操作

**关键代码**:

```python
# src/storage.py
from typing import List, Optional
from formal_science import contract
from .models import Todo, TodoStatus

class TodoStorage:
    """待办事项存储层 - 带验证"""

    def __init__(self, db_path: str = "todo.db"):
        self.db_path = db_path
        self._init_db()

    def _init_db(self):
        """初始化数据库"""
        # 创建表结构
        pass

    @contract(
        pre=["todo is not None"],
        post=["result.id > 0", "self.exists(result.id)"]
    )
    def create(self, todo: Todo) -> Todo:
        """创建待办事项"""
        # 插入数据库
        # 返回带 ID 的实体
        pass

    @contract(
        pre=["todo_id > 0"],
        post=["result is None or result.id == todo_id"]
    )
    def get(self, todo_id: int) -> Optional[Todo]:
        """获取待办事项"""
        pass

    @contract(
        post=["all(t.id > 0 for t in result)"]
    )
    def list_all(self) -> List[Todo]:
        """列出所有待办事项"""
        pass

    @contract(
        pre=["todo_id > 0", "self.exists(todo_id)"],
        post=["not self.exists(todo_id)"]
    )
    def delete(self, todo_id: int) -> bool:
        """删除待办事项"""
        pass

    @contract(
        post=["result == (todo_id in self._cache)"]
    )
    def exists(self, todo_id: int) -> bool:
        """检查待办事项是否存在"""
        pass
```

---

### 第4章：API 层开发 (25:00-35:00)

**目标**: 构建 REST API

**内容**:

1. 设计 API 规范
2. 实现 CRUD 接口
3. 添加输入验证
4. 错误处理

**关键代码**:

```python
# src/api.py
from flask import Flask, request, jsonify
from formal_science import validate_input
from .models import Todo, TodoStatus
from .storage import TodoStorage

app = Flask(__name__)
storage = TodoStorage()

@app.route('/api/todos', methods=['GET'])
def get_todos():
    """获取所有待办事项"""
    status = request.args.get('status')
    todos = storage.list_all()

    if status:
        todos = [t for t in todos if t.status.name.lower() == status.lower()]

    return jsonify([todo_to_dict(t) for t in todos])

@app.route('/api/todos/<int:todo_id>', methods=['GET'])
def get_todo(todo_id: int):
    """获取单个待办事项"""
    todo = storage.get(todo_id)
    if not todo:
        return jsonify({"error": "Todo not found"}), 404
    return jsonify(todo_to_dict(todo))

@app.route('/api/todos', methods=['POST'])
@validate_input({
    "title": {"type": "string", "required": True, "min": 1, "max": 200},
    "description": {"type": "string", "max": 1000},
    "due_date": {"type": "datetime", "optional": True}
})
def create_todo():
    """创建待办事项"""
    data = request.json

    todo = Todo(
        id=0,  # 将由数据库生成
        title=data['title'],
        description=data.get('description', ''),
        status=TodoStatus.PENDING,
        created_at=datetime.now(),
        updated_at=datetime.now(),
        due_date=data.get('due_date')
    )

    created = storage.create(todo)
    return jsonify(todo_to_dict(created)), 201

@app.route('/api/todos/<int:todo_id>/complete', methods=['POST'])
def complete_todo(todo_id: int):
    """完成待办事项"""
    todo = storage.get(todo_id)
    if not todo:
        return jsonify({"error": "Todo not found"}), 404

    try:
        todo.complete()
        storage.update(todo)
        return jsonify(todo_to_dict(todo))
    except AssertionError as e:
        return jsonify({"error": str(e)}), 400

def todo_to_dict(todo: Todo) -> dict:
    """转换 Todo 为字典"""
    return {
        "id": todo.id,
        "title": todo.title,
        "description": todo.description,
        "status": todo.status.name,
        "created_at": todo.created_at.isoformat(),
        "updated_at": todo.updated_at.isoformat(),
        "due_date": todo.due_date.isoformat() if todo.due_date else None
    }
```

---

### 第5章：前端界面 (35:00-40:00)

**目标**: 创建简单的前端界面

**内容**:

1. 设计界面布局
2. 实现与 API 的交互
3. 添加基本样式

**关键代码**:

```html
<!-- templates/index.html -->
<!DOCTYPE html>
<html>
<head>
    <title>Todo App - 经过验证的待办事项</title>
    <style>
        body {
            font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, sans-serif;
            max-width: 800px;
            margin: 0 auto;
            padding: 20px;
            background: #f5f5f5;
        }
        .header {
            text-align: center;
            margin-bottom: 30px;
        }
        .header h1 {
            color: #333;
            margin-bottom: 10px;
        }
        .header .badge {
            display: inline-block;
            background: #4CAF50;
            color: white;
            padding: 5px 15px;
            border-radius: 20px;
            font-size: 14px;
        }
        .todo-form {
            background: white;
            padding: 20px;
            border-radius: 8px;
            margin-bottom: 20px;
            box-shadow: 0 2px 4px rgba(0,0,0,0.1);
        }
        .todo-form input, .todo-form textarea {
            width: 100%;
            padding: 10px;
            margin-bottom: 10px;
            border: 1px solid #ddd;
            border-radius: 4px;
            box-sizing: border-box;
        }
        .todo-form button {
            background: #2196F3;
            color: white;
            border: none;
            padding: 10px 20px;
            border-radius: 4px;
            cursor: pointer;
        }
        .todo-list {
            background: white;
            border-radius: 8px;
            box-shadow: 0 2px 4px rgba(0,0,0,0.1);
        }
        .todo-item {
            padding: 15px 20px;
            border-bottom: 1px solid #eee;
            display: flex;
            justify-content: space-between;
            align-items: center;
        }
        .todo-item:last-child {
            border-bottom: none;
        }
        .todo-status {
            display: inline-block;
            padding: 3px 10px;
            border-radius: 12px;
            font-size: 12px;
            font-weight: bold;
        }
        .status-pending { background: #FFC107; color: #333; }
        .status-in_progress { background: #2196F3; color: white; }
        .status-completed { background: #4CAF50; color: white; }
        .status-cancelled { background: #9E9E9E; color: white; }
    </style>
</head>
<body>
    <div class="header">
        <h1>📝 Todo App</h1>
        <span class="badge">✓ 经过形式化验证</span>
    </div>

    <div class="todo-form">
        <h3>添加新待办</h3>
        <input type="text" id="title" placeholder="标题" maxlength="200">
        <textarea id="description" placeholder="描述（可选）" maxlength="1000"></textarea>
        <button onclick="addTodo()">添加</button>
    </div>

    <div class="todo-list" id="todoList">
        <!-- 待办事项列表 -->
    </div>

    <script>
        const API_BASE = '/api/todos';

        // 加载待办事项
        async function loadTodos() {
            const response = await fetch(API_BASE);
            const todos = await response.json();
            renderTodos(todos);
        }

        // 渲染待办列表
        function renderTodos(todos) {
            const container = document.getElementById('todoList');
            if (todos.length === 0) {
                container.innerHTML = '<div class="todo-item">暂无待办事项</div>';
                return;
            }

            container.innerHTML = todos.map(todo => `
                <div class="todo-item">
                    <div>
                        <strong>${escapeHtml(todo.title)}</strong>
                        <p>${escapeHtml(todo.description || '')}</p>
                        <span class="todo-status status-${todo.status.toLowerCase()}">
                            ${translateStatus(todo.status)}
                        </span>
                    </div>
                    <div>
                        ${todo.status === 'PENDING' ?
                            `<button onclick="startTodo(${todo.id})">开始</button>` : ''}
                        ${todo.status === 'IN_PROGRESS' ?
                            `<button onclick="completeTodo(${todo.id})">完成</button>` : ''}
                    </div>
                </div>
            `).join('');
        }

        // 添加待办
        async function addTodo() {
            const title = document.getElementById('title').value.trim();
            const description = document.getElementById('description').value.trim();

            if (!title) {
                alert('标题不能为空');
                return;
            }

            const response = await fetch(API_BASE, {
                method: 'POST',
                headers: {'Content-Type': 'application/json'},
                body: JSON.stringify({title, description})
            });

            if (response.ok) {
                document.getElementById('title').value = '';
                document.getElementById('description').value = '';
                loadTodos();
            } else {
                const error = await response.json();
                alert('添加失败: ' + error.error);
            }
        }

        // 完成待办
        async function completeTodo(id) {
            const response = await fetch(`${API_BASE}/${id}/complete`, {
                method: 'POST'
            });

            if (response.ok) {
                loadTodos();
            } else {
                const error = await response.json();
                alert('操作失败: ' + error.error);
            }
        }

        // 辅助函数
        function escapeHtml(text) {
            const div = document.createElement('div');
            div.textContent = text;
            return div.innerHTML;
        }

        function translateStatus(status) {
            const map = {
                'PENDING': '待处理',
                'IN_PROGRESS': '进行中',
                'COMPLETED': '已完成',
                'CANCELLED': '已取消'
            };
            return map[status] || status;
        }

        // 初始化
        loadTodos();
    </script>
</body>
</html>
```

---

### 第6章：测试与验证 (40:00-43:00)

**目标**: 全面测试和验证应用

**内容**:

1. 编写单元测试
2. 运行形式化验证
3. 集成测试
4. 性能测试

**测试代码**:

```python
# tests/test_models.py
import pytest
from datetime import datetime
from src.models import Todo, TodoStatus

class TestTodo:
    """Todo 模型测试"""

    def test_create_valid_todo(self):
        """测试创建有效待办"""
        todo = Todo(
            id=1,
            title="测试待办",
            description="描述",
            status=TodoStatus.PENDING,
            created_at=datetime.now(),
            updated_at=datetime.now()
        )
        assert todo.title == "测试待办"
        assert todo.status == TodoStatus.PENDING

    def test_empty_title_raises_error(self):
        """测试空标题应报错"""
        with pytest.raises(AssertionError):
            Todo(
                id=1,
                title="",  # 空标题
                description="描述",
                status=TodoStatus.PENDING,
                created_at=datetime.now(),
                updated_at=datetime.now()
            )

    def test_complete_todo(self):
        """测试完成待办"""
        todo = Todo(
            id=1,
            title="测试",
            description="",
            status=TodoStatus.IN_PROGRESS,
            created_at=datetime.now(),
            updated_at=datetime.now()
        )
        todo.complete()
        assert todo.status == TodoStatus.COMPLETED

    def test_complete_already_completed_raises_error(self):
        """测试重复完成应报错"""
        todo = Todo(
            id=1,
            title="测试",
            description="",
            status=TodoStatus.COMPLETED,
            created_at=datetime.now(),
            updated_at=datetime.now()
        )
        with pytest.raises(AssertionError):
            todo.complete()
```

**验证命令**:

```bash
# 运行形式化验证
formal-verify src/ --report verification_report.json

# 运行单元测试
pytest tests/ -v --cov=src

# 集成测试
python -m pytest tests/test_integration.py
```

---

### 第7章：部署与总结 (43:00-45:00)

**目标**: 部署应用，总结项目

**内容**:

1. 生产环境配置
2. 部署到服务器
3. 项目回顾
4. 扩展建议

**部署配置**:

```python
# src/config.py
import os

class Config:
    """应用配置"""
    SECRET_KEY = os.environ.get('SECRET_KEY') or 'dev-secret-key'
    DATABASE_PATH = os.environ.get('DATABASE_PATH') or 'todo.db'
    DEBUG = False

class DevelopmentConfig(Config):
    DEBUG = True

class ProductionConfig(Config):
    DEBUG = False
    # 生产环境特定配置
```

**总结要点**:

```
项目完成清单:
✓ 数据模型设计 + 验证
✓ 存储层实现
✓ REST API 开发
✓ 前端界面
✓ 单元测试
✓ 形式化验证
✓ 部署配置

学到的技能:
• 形式化验证实践
• 契约式编程
• 状态机设计
• API 开发
• 测试驱动开发
```

**扩展建议**:

```
可能的扩展:
• 用户认证系统
• 待办事项分类/标签
• 优先级管理
• 提醒功能
• 团队协作
• 移动端适配
• 更多验证（如并发安全）
```

---

## 制作备注

### 时间分配

| 章节 | 时间 | 主要内容 |
|-----|------|---------|
| 项目初始化 | 5分钟 | 环境搭建 |
| 数据模型 | 10分钟 | 核心设计+验证 |
| 存储层 | 10分钟 | 数据持久化 |
| API 开发 | 10分钟 | REST 接口 |
| 前端界面 | 5分钟 | 简单 UI |
| 测试验证 | 3分钟 | 质量保证 |
| 部署总结 | 2分钟 | 收尾 |

### 录制建议

- 提前准备好完整的项目代码
- 使用代码片段加速演示
- 重点讲解验证部分
- 准备好应对常见错误的方案

---

## 版本记录

| 版本 | 日期 | 修改内容 | 作者 |
|-----|------|---------|------|
| v1.0 | - | 初始版本 | - |
