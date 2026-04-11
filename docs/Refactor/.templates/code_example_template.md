---
title: "代码示例标题"
date: YYYY-MM-DD
author: "作者名称"
language: "python"  # 主要编程语言
difficulty: "beginner"  # beginner | intermediate | advanced
tags: ["示例", "代码", "教程"]
---

# 代码示例标题

> 简要描述代码示例的功能和用途

## 示例概览

### 功能说明

详细描述代码实现的功能。

### 适用场景

- 场景1：说明场景1
- 场景2：说明场景2
- 场景3：说明场景3

### 技术栈

- 语言/框架 1
- 语言/框架 2
- 依赖库 3

---

## 完整代码

### 文件头模板

```python
#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
文件名: example.py
描述: 简短描述文件功能
作者: 作者名称
日期: YYYY-MM-DD
版本: 1.0.0

使用示例:
    python example.py --input input.txt --output output.txt

依赖:
    - package1>=1.0.0
    - package2>=2.0.0

变更历史:
    1.0.0 (YYYY-MM-DD): 初始版本
"""

__version__ = "1.0.0"
__author__ = "作者名称"

# 代码正文...
```

---

## 分步详解

### 步骤 1: 导入依赖

```python
import os
import sys
from typing import List, Dict, Optional
from datetime import datetime

# 第三方库
import requests
from pydantic import BaseModel
```

**说明**: 解释为什么需要这些导入。

---

### 步骤 2: 定义数据结构

```python
class User(BaseModel):
    """用户数据模型"""
    id: int
    name: str
    email: str
    created_at: datetime

    class Config:
        json_encoders = {
            datetime: lambda v: v.isoformat()
        }
```

**说明**: 解释数据结构的用途。

---

### 步骤 3: 实现核心功能

```python
def fetch_users(api_url: str) -> List[User]:
    """
    从API获取用户列表

    Args:
        api_url: API端点URL

    Returns:
        用户对象列表

    Raises:
        requests.RequestException: 当API请求失败时
    """
    try:
        response = requests.get(api_url, timeout=30)
        response.raise_for_status()
        data = response.json()
        return [User(**user) for user in data]
    except requests.RequestException as e:
        print(f"Error fetching users: {e}")
        raise
```

**说明**: 解释核心逻辑的实现思路。

---

### 步骤 4: 主程序入口

```python
def main():
    """主函数"""
    api_url = "https://api.example.com/users"

    print(f"Fetching users from {api_url}...")
    users = fetch_users(api_url)

    print(f"Found {len(users)} users:")
    for user in users:
        print(f"  - {user.name} ({user.email})")


if __name__ == "__main__":
    main()
```

---

## 多语言示例

### Python 版本

```python
def greet(name: str) -> str:
    return f"Hello, {name}!"

print(greet("World"))
```

### JavaScript 版本

```javascript
function greet(name) {
    return `Hello, ${name}!`;
}

console.log(greet("World"));
```

### TypeScript 版本

```typescript
function greet(name: string): string {
    return `Hello, ${name}!`;
}

console.log(greet("World"));
```

### Rust 版本

```rust
fn greet(name: &str) -> String {
    format!("Hello, {}!", name)
}

fn main() {
    println!("{}", greet("World"));
}
```

### Go 版本

```go
package main

import "fmt"

func greet(name string) string {
    return fmt.Sprintf("Hello, %s!", name)
}

func main() {
    fmt.Println(greet("World"))
}
```

---

## 输出示例

### 标准输出

```
Fetching users from https://api.example.com/users...
Found 3 users:
  - Alice (alice@example.com)
  - Bob (bob@example.com)
  - Carol (carol@example.com)
```

### JSON 输出

```json
{
  "status": "success",
  "data": {
    "users": [
      {
        "id": 1,
        "name": "Alice",
        "email": "alice@example.com"
      },
      {
        "id": 2,
        "name": "Bob",
        "email": "bob@example.com"
      }
    ],
    "total": 2
  },
  "timestamp": "2024-01-01T12:00:00Z"
}
```

### 表格输出

| ID | 名称 | 邮箱 | 状态 |
|----|------|------|------|
| 1 | Alice | alice@example.com | 活跃 |
| 2 | Bob | bob@example.com | 活跃 |
| 3 | Carol | carol@example.com | 离线 |

---

## 常见错误与解决

### 错误 1: 连接超时

```
requests.exceptions.ConnectTimeout:
    HTTPConnectionPool(host='api.example.com', port=80):
    Max retries exceeded with url: /users
```

**原因**: 网络连接问题或API服务器无响应。

**解决**: 检查网络连接，增加超时时间，或检查API服务状态。

### 错误 2: JSON 解析错误

```
json.decoder.JSONDecodeError: Expecting value: line 1 column 1 (char 0)
```

**原因**: API返回的不是有效的JSON格式。

**解决**: 检查API响应内容，确认Content-Type头信息。

---

## 扩展阅读

- [官方文档](https://docs.example.com)
- [API 参考](https://api.example.com/docs)
- [最佳实践指南](../best-practices.md)
