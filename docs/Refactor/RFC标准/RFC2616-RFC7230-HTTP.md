# RFC 2616/7230 - Hypertext Transfer Protocol (HTTP)

## 1. RFC概述

### 1.1 基本信息

- **RFC编号**: RFC 2616 / RFC 7230-7235
- **标题**: Hypertext Transfer Protocol -- HTTP/1.1
- **发布日期**: RFC 2616: 1999年6月 / RFC 7230-7235: 2014年6月
- **状态**: RFC 2616已废弃，由RFC 7230-7235替代
- **相关**: RFC 1945 (HTTP/1.0), RFC 7540 (HTTP/2), RFC 9114 (HTTP/3)

### 1.2 历史背景

HTTP是万维网（WWW）的基础协议。RFC 2616定义了HTTP/1.1，修复了HTTP/1.0的诸多问题，引入了持久连接、分块传输、缓存控制等重要特性。2014年，RFC 7230-7235系列对HTTP/1.1进行了清理和重构，废弃了RFC 2616。

### 1.3 核心贡献

- 定义了请求-响应协议模型
- 引入持久连接减少延迟
- 标准化缓存控制机制
- 定义丰富的请求方法和状态码
- 支持内容协商和编码

---

## 2. 协议详细说明

### 2.1 HTTP架构

#### 2.1.1 客户端-服务器模型

```
+-------------+                    +-------------+
|   Client    | <----------------> |   Server    |
| (User Agent)|     Request/       |   (Origin   |
|             |     Response       |   Server)   |
+-------------+                    +-------------+
       |                                  |
       |    +---------------------+       |
       +--->|   Intermediaries    |<------+
            | (Proxy, Gateway,    |
            |  Tunnel, Cache)     |
            +---------------------+
```

#### 2.1.2 无状态协议

- 每个请求独立处理
- 无服务器端会话状态
- 通过Cookie等机制维护状态

#### 2.1.3 可扩展设计

- 头部字段可扩展
- 方法可扩展
- 状态码可扩展

### 2.2 HTTP方法

| 方法 | 描述 | 幂等性 | 安全性 | RFC |
|------|------|--------|--------|-----|
| GET | 获取资源 | 是 | 是 | 7231 |
| HEAD | 获取头部 | 是 | 是 | 7231 |
| POST | 提交数据 | 否 | 否 | 7231 |
| PUT | 替换资源 | 是 | 否 | 7231 |
| DELETE | 删除资源 | 是 | 否 | 7231 |
| OPTIONS | 查询支持方法 | 是 | 是 | 7231 |
| TRACE | 追踪路径 | 是 | 是 | 7231 |
| PATCH | 部分更新 | 否 | 否 | 5789 |
| CONNECT | 建立隧道 | - | - | 7231 |

### 2.3 核心机制

#### 2.3.1 持久连接（Keep-Alive）

```
Connection: keep-alive
Keep-Alive: timeout=5, max=100
```

#### 2.3.2 分块传输编码（Chunked Transfer Coding）

```
Transfer-Encoding: chunked

5\r\n          <-- 块大小（十六进制）
Hello\r\n     <-- 数据
7\r\n
 World!\r\n
0\r\n          <-- 结束标记
\r\n
```

#### 2.3.3 内容协商

- **Accept**: 可接受的媒体类型
- **Accept-Encoding**: 可接受的内容编码
- **Accept-Language**: 可接受的语言
- **Accept-Charset**: 可接受的字符集

---

## 3. 报文格式

### 3.1 HTTP/1.1报文结构

**请求报文**:

```
<method> <request-target> <HTTP-version>\r\n
<header-field>: <value>\r\n
...
\n
\r\n
[<message-body>]
```

**响应报文**:

```
<HTTP-version> <status-code> <reason-phrase>\r\n
<header-field>: <value>\r\n
...
\n
\r\n
[<message-body>]
```

### 3.2 请求行格式

```
GET /index.html HTTP/1.1\r\n
POST /api/users HTTP/1.1\r\n
DELETE /api/users/123 HTTP/1.1\r\n
```

### 3.3 状态行格式

```
HTTP/1.1 200 OK\r\n
HTTP/1.1 404 Not Found\r\n
HTTP/1.1 500 Internal Server Error\r\n
```

### 3.4 状态码分类

| 类别 | 范围 | 描述 |
|------|------|------|
| 1xx | 100-199 | 信息响应 |
| 2xx | 200-299 | 成功 |
| 3xx | 300-399 | 重定向 |
| 4xx | 400-499 | 客户端错误 |
| 5xx | 500-599 | 服务器错误 |

### 3.5 常见状态码

| 状态码 | 原因短语 | 描述 |
|--------|----------|------|
| 200 | OK | 请求成功 |
| 201 | Created | 资源创建成功 |
| 204 | No Content | 成功但无返回内容 |
| 301 | Moved Permanently | 永久重定向 |
| 302 | Found | 临时重定向 |
| 304 | Not Modified | 缓存有效 |
| 400 | Bad Request | 请求格式错误 |
| 401 | Unauthorized | 需要认证 |
| 403 | Forbidden | 禁止访问 |
| 404 | Not Found | 资源不存在 |
| 405 | Method Not Allowed | 方法不允许 |
| 500 | Internal Server Error | 服务器内部错误 |
| 502 | Bad Gateway | 网关错误 |
| 503 | Service Unavailable | 服务不可用 |
| 504 | Gateway Timeout | 网关超时 |

### 3.6 常见头部字段

**通用首部**:

| 字段 | 描述 |
|------|------|
| Cache-Control | 缓存控制指令 |
| Connection | 连接管理 |
| Date | 消息创建时间 |
| Transfer-Encoding | 传输编码 |
| Upgrade | 协议升级 |
| Via | 代理信息 |

**请求首部**:

| 字段 | 描述 |
|------|------|
| Host | 目标主机（必需） |
| User-Agent | 客户端标识 |
| Accept | 可接受媒体类型 |
| Accept-Encoding | 可接受编码 |
| Authorization | 认证信息 |
| Cookie | Cookie数据 |
| Referer | 来源页面 |

**响应首部**:

| 字段 | 描述 |
|------|------|
| Server | 服务器标识 |
| Location | 重定向目标 |
| Set-Cookie | 设置Cookie |
| ETag | 实体标签 |
| Last-Modified | 最后修改时间 |
| Content-Type | 内容类型 |
| Content-Length | 内容长度 |

---

## 4. 状态机

### 4.1 HTTP连接状态机

```
                    +------------------+
                    |      IDLE        |
                    +--------+---------+
                             |
                    Request received
                             |
                             v
                    +--------+---------+
                    |  READ REQUEST    |
                    |  HEADERS         |
                    +--------+---------+
                             |
                             v
                    +--------+---------+
                    |  READ BODY       | (if any)
                    +--------+---------+
                             |
                             v
                    +--------+---------+
                    |  PROCESSING      |
                    +--------+---------+
                             |
                             v
                    +--------+---------+
                    |  SEND RESPONSE   |
                    |  HEADERS         |
                    +--------+---------+
                             |
                             v
                    +--------+---------+
                    |  SEND BODY       | (if any)
                    +--------+---------+
                             |
              +--------------+--------------+
              |                             |
        Connection:                Connection:
        keep-alive                   close
              |                             |
              v                             v
    +---------+---------+      +----------+----------+
    |  RETURN TO IDLE   |      |    CLOSE            |
    |  (wait next req)  |      |    CONNECTION       |
    +---------+---------+      +----------+----------+
              |                             |
              v                             v
    +---------+---------+      +----------+----------+
    |  (timeout check)  |      |  CLEANUP            |
    |  Close idle conn  |      +---------------------+
    +---------+---------+
              |
              v
    +---------+---------+
    |    CLOSE          |
    +-------------------+
```

### 4.2 请求处理状态机

```
                    +------------------+
                    |   START          |
                    +--------+---------+
                             |
                             v
                    +--------+---------+
                    |  PARSE REQUEST   |
                    |  LINE            |
                    +--------+---------+
                             |
              +--------------+--------------+
              |                             |
        Valid                        Invalid
              |                             |
              v                             v
    +---------+---------+      +----------+----------+
    |  PARSE HEADERS    |      |  SEND 400           |
    +---------+---------+      |  Bad Request        |
              |                +----------+----------+
    +---------+---------+                 |
    |                   |                 v
 Valid             Invalid      +----------+----------+
    |                   |      |  CLOSE CONNECTION   |
    v                   v      +---------------------+
+---+---+         +-----+-----+
| CHECK |         | SEND 400  |
| HOST  |         +-----+-----+
+---+---+               |
    |                   v
    |            +------+------+
    |            |    CLOSE    |
    v            +-------------+
+---+---+
|Valid |
| HOST |
+---+---+
    |
    v
+---+---+         +-----+-----+
| ROUTE |         | SEND 404  |
|REQUEST|         | Not Found |
+---+---+         +-----+-----+
    |                   |
Valid              Invalid
    |                   |
    v                   v
+---+---+         +-----+-----+
|CHECK  |         |   SEND    |
|METHOD |         |   405     |
+---+---+         +-----+-----+
    |                   |
Allowed         Not Allowed
    |                   |
    v                   v
+---+---+         +-----+-----+
|AUTH   |         |   SEND    |
|CHECK  |         |   401     |
+---+---+         +-----+-----+
    |
    v
+---+---+         +-----+-----+
|PROCESS|         | SEND 500  |
|REQUEST|         |   Error   |
+---+---+         +-----+-----+
    |                   |
Success            Error
    |                   |
    v                   v
+---+---+         +-----+-----+
| BUILD |         |   SEND    |
|RESPONSE|        |   500     |
+---+---+         +-----+-----+
    |                   |
    +---------+---------+
              |
              v
    +---------+---------+
    |    SEND RESPONSE  |
    +-------------------+
```

---

## 5. 安全性考虑

### 5.1 HTTP安全威胁

#### 5.1.1 中间人攻击（MITM）

- **攻击方式**: 拦截和篡改通信
- **影响**: 数据泄露、会话劫持
- **缓解措施**: 使用HTTPS（TLS/SSL）

#### 5.1.2 会话劫持

- **攻击方式**: 窃取会话标识符
- **影响**: 冒充合法用户
- **缓解措施**:
  - 安全Cookie属性（Secure, HttpOnly, SameSite）
  - 会话超时
  - IP绑定

#### 5.1.3 CSRF攻击

- **攻击方式**: 诱导用户执行非预期操作
- **影响**: 非授权操作
- **缓解措施**:
  - CSRF Token
  - SameSite Cookie
  - Referer检查

#### 5.1.4 注入攻击

- **类型**: SQL注入、XSS、命令注入
- **缓解措施**:
  - 输入验证
  - 输出编码
  - 参数化查询

### 5.2 安全头部

| 头部 | 描述 | 示例 |
|------|------|------|
| Strict-Transport-Security | 强制HTTPS | max-age=31536000; includeSubDomains |
| Content-Security-Policy | 内容安全策略 | default-src 'self' |
| X-Frame-Options | 点击劫持防护 | DENY, SAMEORIGIN |
| X-Content-Type-Options | MIME类型嗅探防护 | nosniff |
| X-XSS-Protection | XSS过滤器 | 1; mode=block |
| Referrer-Policy | Referrer策略 | strict-origin-when-cross-origin |

### 5.3 HTTPS/TLS

```
HTTP + TLS = HTTPS

TLS握手过程:
1. Client Hello (支持的加密套件)
2. Server Hello (选择的加密套件) + Certificate
3. Client验证证书，生成预主密钥
4. 双方生成会话密钥
5. 加密通信开始
```

---

## 6. 与教材对标的章节

### 6.1 《计算机网络：自顶向下方法》

| RFC 7230内容 | 对应章节 |
|-------------|----------|
| HTTP概述 | 第2章：应用层 - 2.2 Web和HTTP |
| 持久连接 | 2.2.2 非持续连接和持续连接 |
| HTTP报文格式 | 2.2.3 HTTP报文格式 |
| Cookie | 2.2.4 用户与服务器的交互：Cookie |
| Web缓存 | 2.2.5 Web缓存 |
| 条件GET | 2.2.6 条件GET方法 |

### 6.2 《HTTP权威指南》

| RFC 7230内容 | 对应章节 |
|-------------|----------|
| HTTP协议 | 第3部分：识别、认证与安全 |
| 报文 | 第3章：HTTP报文 |
| 连接管理 | 第4章：连接管理 |
| 缓存 | 第7章：缓存 |

### 6.3 《图解HTTP》

| RFC 7230内容 | 对应章节 |
|-------------|----------|
| HTTP协议 | 第2章：简单的HTTP协议 |
| 状态码 | 第4章：返回结果的HTTP状态码 |
| 首部 | 第6章：HTTP首部 |
| HTTPS | 第7章：确保Web安全的HTTPS |

---

## 7. 实现示例

### 7.1 Python实现：HTTP服务器

```python
import socket
import threading
import re
from dataclasses import dataclass, field
from typing import Dict, Optional, Callable, List
from enum import IntEnum
from datetime import datetime
import urllib.parse

class HTTPMethod(IntEnum):
    """HTTP方法"""
    GET = 1
    HEAD = 2
    POST = 3
    PUT = 4
    DELETE = 5
    OPTIONS = 6
    TRACE = 7
    PATCH = 8
    CONNECT = 9

class HTTPStatus(IntEnum):
    """HTTP状态码"""
    OK = 200
    CREATED = 201
    NO_CONTENT = 204
    MOVED_PERMANENTLY = 301
    FOUND = 302
    NOT_MODIFIED = 304
    BAD_REQUEST = 400
    UNAUTHORIZED = 401
    FORBIDDEN = 403
    NOT_FOUND = 404
    METHOD_NOT_ALLOWED = 405
    INTERNAL_ERROR = 500
    NOT_IMPLEMENTED = 501
    BAD_GATEWAY = 502
    SERVICE_UNAVAILABLE = 503

STATUS_PHRASES = {
    200: "OK",
    201: "Created",
    204: "No Content",
    301: "Moved Permanently",
    302: "Found",
    304: "Not Modified",
    400: "Bad Request",
    401: "Unauthorized",
    403: "Forbidden",
    404: "Not Found",
    405: "Method Not Allowed",
    500: "Internal Server Error",
    501: "Not Implemented",
    502: "Bad Gateway",
    503: "Service Unavailable",
}

@dataclass
class HTTPRequest:
    """HTTP请求"""
    method: str
    path: str
    version: str
    headers: Dict[str, str] = field(default_factory=dict)
    body: bytes = b''
    query_params: Dict[str, List[str]] = field(default_factory=dict)

    @classmethod
    def parse(cls, data: bytes) -> 'HTTPRequest':
        """解析HTTP请求"""
        try:
            # 分离首部和主体
            header_end = data.find(b'\r\n\r\n')
            if header_end == -1:
                raise ValueError("Invalid HTTP request: no header-body separator")

            header_data = data[:header_end].decode('utf-8', errors='replace')
            body = data[header_end + 4:]

            # 解析请求行
            lines = header_data.split('\r\n')
            request_line = lines[0]
            parts = request_line.split(' ')

            if len(parts) < 2:
                raise ValueError("Invalid request line")

            method = parts[0]
            target = parts[1]
            version = parts[2] if len(parts) > 2 else 'HTTP/1.1'

            # 解析路径和查询参数
            if '?' in target:
                path, query_string = target.split('?', 1)
                query_params = urllib.parse.parse_qs(query_string)
            else:
                path = target
                query_params = {}

            # 解析头部
            headers = {}
            for line in lines[1:]:
                if ':' in line:
                    key, value = line.split(':', 1)
                    headers[key.strip().lower()] = value.strip()

            # 解析body长度
            content_length = int(headers.get('content-length', 0))
            if content_length > 0:
                body = body[:content_length]

            return cls(
                method=method,
                path=path,
                version=version,
                headers=headers,
                body=body,
                query_params=query_params
            )
        except Exception as e:
            raise ValueError(f"Failed to parse HTTP request: {e}")

    def get_header(self, name: str) -> Optional[str]:
        """获取头部值"""
        return self.headers.get(name.lower())

@dataclass
class HTTPResponse:
    """HTTP响应"""
    status: int
    headers: Dict[str, str] = field(default_factory=dict)
    body: bytes = b''
    version: str = 'HTTP/1.1'

    def __post_init__(self):
        # 设置默认头部
        if 'content-type' not in self.headers:
            self.headers['content-type'] = 'text/html; charset=utf-8'
        if 'date' not in self.headers:
            self.headers['date'] = datetime.utcnow().strftime('%a, %d %b %Y %H:%M:%S GMT')
        if 'server' not in self.headers:
            self.headers['server'] = 'SimpleHTTP/1.0'

    def build(self) -> bytes:
        """构建HTTP响应"""
        # 状态行
        status_phrase = STATUS_PHRASES.get(self.status, 'Unknown')
        response = f"{self.version} {self.status} {status_phrase}\r\n"

        # 设置Content-Length
        self.headers['content-length'] = str(len(self.body))

        # 头部
        for key, value in self.headers.items():
            response += f"{key}: {value}\r\n"

        # 空行
        response += '\r\n'

        return response.encode('utf-8') + self.body

    @classmethod
    def ok(cls, body: bytes = b'', content_type: str = 'text/html') -> 'HTTPResponse':
        """创建200 OK响应"""
        headers = {'content-type': content_type}
        return cls(status=200, headers=headers, body=body)

    @classmethod
    def not_found(cls, message: str = "Not Found") -> 'HTTPResponse':
        """创建404响应"""
        body = f"<h1>404 {message}</h1>".encode('utf-8')
        return cls(status=404, body=body)

    @classmethod
    def redirect(cls, location: str, permanent: bool = False) -> 'HTTPResponse':
        """创建重定向响应"""
        status = 301 if permanent else 302
        headers = {'location': location}
        return cls(status=status, headers=headers)


class HTTPServer:
    """简单HTTP服务器"""

    def __init__(self, host: str = '0.0.0.0', port: int = 8080):
        self.host = host
        self.port = port
        self.routes: Dict[str, Dict[str, Callable]] = {}
        self.middlewares: List[Callable] = []
        self.server_socket = None
        self.running = False

    def route(self, path: str, methods: List[str] = None):
        """路由装饰器"""
        if methods is None:
            methods = ['GET']
        methods = [m.upper() for m in methods]

        def decorator(func: Callable):
            if path not in self.routes:
                self.routes[path] = {}
            for method in methods:
                self.routes[path][method] = func
            return func
        return decorator

    def add_middleware(self, middleware: Callable):
        """添加中间件"""
        self.middlewares.append(middleware)

    def handle_request(self, request: HTTPRequest) -> HTTPResponse:
        """处理HTTP请求"""
        # 执行中间件
        for middleware in self.middlewares:
            response = middleware(request)
            if response:
                return response

        # 路由匹配
        path = request.path
        method = request.method.upper()

        # 精确匹配
        if path in self.routes and method in self.routes[path]:
            try:
                return self.routes[path][method](request)
            except Exception as e:
                return HTTPResponse(
                    status=500,
                    body=f"<h1>500 Internal Server Error</h1><p>{str(e)}</p>".encode('utf-8')
                )

        # 尝试模式匹配
        for route_path, handlers in self.routes.items():
            pattern = route_path.replace('*', '.*').replace('{', '(?P<').replace('}', '>[^/]+)')
            match = re.match(f'^{pattern}$', path)
            if match and method in handlers:
                try:
                    request.path_params = match.groupdict()
                    return handlers[method](request)
                except Exception as e:
                    return HTTPResponse(
                        status=500,
                        body=f"<h1>500 Internal Server Error</h1><p>{str(e)}</p>".encode('utf-8')
                    )

        return HTTPResponse.not_found()

    def handle_client(self, client_socket: socket.socket, addr: tuple):
        """处理客户端连接"""
        try:
            # 设置超时
            client_socket.settimeout(30)

            # 读取请求
            data = b''
            while True:
                chunk = client_socket.recv(4096)
                if not chunk:
                    break
                data += chunk

                # 检查是否收到完整请求头
                if b'\r\n\r\n' in data:
                    # 检查Content-Length
                    header_end = data.find(b'\r\n\r\n')
                    headers_data = data[:header_end].decode('utf-8', errors='replace')

                    content_length = 0
                    for line in headers_data.split('\r\n'):
                        if line.lower().startswith('content-length:'):
                            content_length = int(line.split(':')[1].strip())
                            break

                    # 检查是否收到完整主体
                    if len(data) >= header_end + 4 + content_length:
                        break

            if not data:
                return

            # 解析请求
            try:
                request = HTTPRequest.parse(data)
                print(f"[HTTP] {request.method} {request.path} from {addr}")
            except ValueError as e:
                response = HTTPResponse(status=400, body=b'Bad Request')
                client_socket.send(response.build())
                return

            # 处理请求
            response = self.handle_request(request)

            # 发送响应
            client_socket.send(response.build())

            # 检查连接是否保持
            connection = request.get_header('connection')
            if connection and connection.lower() == 'keep-alive':
                # 保持连接，继续处理下一个请求
                pass

        except socket.timeout:
            print(f"[HTTP] Client {addr} timeout")
        except Exception as e:
            print(f"[HTTP] Error handling client {addr}: {e}")
        finally:
            client_socket.close()

    def start(self):
        """启动服务器"""
        self.server_socket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        self.server_socket.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        self.server_socket.bind((self.host, self.port))
        self.server_socket.listen(5)

        self.running = True
        print(f"[HTTP] Server started on http://{self.host}:{self.port}")

        try:
            while self.running:
                client_socket, addr = self.server_socket.accept()
                # 创建线程处理客户端
                thread = threading.Thread(
                    target=self.handle_client,
                    args=(client_socket, addr),
                    daemon=True
                )
                thread.start()
        except KeyboardInterrupt:
            print("\n[HTTP] Shutting down...")
        finally:
            self.stop()

    def stop(self):
        """停止服务器"""
        self.running = False
        if self.server_socket:
            self.server_socket.close()


# 使用示例
if __name__ == "__main__":
    app = HTTPServer(host='127.0.0.1', port=8080)

    @app.route('/', methods=['GET'])
    def index(request: HTTPRequest) -> HTTPResponse:
        html = b"""
        <!DOCTYPE html>
        <html>
        <head><title>Simple HTTP Server</title></head>
        <body>
            <h1>Welcome to Simple HTTP Server</h1>
            <p>Endpoints:</p>
            <ul>
                <li><a href="/hello">/hello</a> - GET greeting</li>
                <li><a href="/api/status">/api/status</a> - API status</li>
            </ul>
        </body>
        </html>
        """
        return HTTPResponse.ok(body=html)

    @app.route('/hello', methods=['GET'])
    def hello(request: HTTPRequest) -> HTTPResponse:
        name = request.query_params.get('name', ['World'])[0]
        html = f"<h1>Hello, {name}!</h1>".encode('utf-8')
        return HTTPResponse.ok(body=html)

    @app.route('/api/status', methods=['GET'])
    def status(request: HTTPRequest) -> HTTPResponse:
        import json
        data = {
            'status': 'ok',
            'timestamp': datetime.utcnow().isoformat(),
            'version': '1.0'
        }
        return HTTPResponse.ok(
            body=json.dumps(data).encode('utf-8'),
            content_type='application/json'
        )

    @app.route('/redirect', methods=['GET'])
    def redirect_example(request: HTTPRequest) -> HTTPResponse:
        return HTTPResponse.redirect('/', permanent=False)

    # 启动服务器
    print("Starting HTTP server...")
    print("Try: curl http://127.0.0.1:8080/")
    # app.start()  # 取消注释以启动服务器
```

### 7.2 HTTP客户端实现

```python
import socket
import ssl
import urllib.parse
from typing import Optional, Dict, List, Tuple

class HTTPClient:
    """简单HTTP客户端"""

    def __init__(self, timeout: float = 30.0):
        self.timeout = timeout
        self.default_headers = {
            'User-Agent': 'SimpleHTTPClient/1.0',
            'Accept': '*/*',
            'Accept-Encoding': 'identity',
            'Connection': 'close'
        }

    def request(self, method: str, url: str,
                headers: Optional[Dict[str, str]] = None,
                body: Optional[bytes] = None) -> HTTPResponse:
        """发送HTTP请求"""
        # 解析URL
        parsed = urllib.parse.urlparse(url)

        is_https = parsed.scheme == 'https'
        host = parsed.hostname
        port = parsed.port or (443 if is_https else 80)
        path = parsed.path or '/'
        if parsed.query:
            path += '?' + parsed.query

        # 构建请求
        request_lines = [f"{method.upper()} {path} HTTP/1.1"]

        # 合并头部
        all_headers = self.default_headers.copy()
        if headers:
            all_headers.update(headers)
        all_headers['Host'] = host

        if body:
            all_headers['Content-Length'] = str(len(body))

        for key, value in all_headers.items():
            request_lines.append(f"{key}: {value}")

        request_data = '\r\n'.join(request_lines) + '\r\n\r\n'
        if body:
            request_data = request_data.encode('utf-8') + body
        else:
            request_data = request_data.encode('utf-8')

        # 建立连接
        sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        sock.settimeout(self.timeout)

        try:
            sock.connect((host, port))

            # SSL包装
            if is_https:
                context = ssl.create_default_context()
                sock = context.wrap_socket(sock, server_hostname=host)

            # 发送请求
            sock.send(request_data)

            # 接收响应
            response_data = b''
            while True:
                chunk = sock.recv(4096)
                if not chunk:
                    break
                response_data += chunk

            # 解析响应
            return self._parse_response(response_data)

        finally:
            sock.close()

    def _parse_response(self, data: bytes) -> HTTPResponse:
        """解析HTTP响应"""
        header_end = data.find(b'\r\n\r\n')
        if header_end == -1:
            raise ValueError("Invalid HTTP response")

        header_data = data[:header_end].decode('utf-8', errors='replace')
        body = data[header_end + 4:]

        # 解析状态行
        lines = header_data.split('\r\n')
        status_line = lines[0]
        parts = status_line.split(' ', 2)

        version = parts[0]
        status = int(parts[1])

        # 解析头部
        headers = {}
        for line in lines[1:]:
            if ':' in line:
                key, value = line.split(':', 1)
                headers[key.strip().lower()] = value.strip()

        # 处理分块编码
        if headers.get('transfer-encoding') == 'chunked':
            body = self._decode_chunked(body)

        return HTTPResponse(
            status=status,
            headers=headers,
            body=body,
            version=version
        )

    def _decode_chunked(self, data: bytes) -> bytes:
        """解码分块传输编码"""
        result = b''
        pos = 0

        while pos < len(data):
            # 查找块大小
            line_end = data.find(b'\r\n', pos)
            if line_end == -1:
                break

            size_str = data[pos:line_end].decode('ascii')
            size = int(size_str.split(';')[0], 16)  # 支持扩展

            if size == 0:
                break

            # 读取块数据
            pos = line_end + 2
            result += data[pos:pos + size]
            pos += size + 2  # 跳过\r\n

        return result

    def get(self, url: str, headers: Optional[Dict[str, str]] = None) -> HTTPResponse:
        """GET请求"""
        return self.request('GET', url, headers)

    def post(self, url: str, body: bytes = b'',
             headers: Optional[Dict[str, str]] = None) -> HTTPResponse:
        """POST请求"""
        return self.request('POST', url, headers, body)


# 使用示例
if __name__ == "__main__":
    client = HTTPClient()

    # GET请求示例
    try:
        response = client.get('http://httpbin.org/get')
        print(f"Status: {response.status}")
        print(f"Body: {response.body[:500]}")
    except Exception as e:
        print(f"Error: {e}")
```

---

## 8. 现代应用

### 8.1 HTTP协议的演进

#### 8.1.1 HTTP/2 (RFC 7540)

- 二进制分帧层
- 多路复用
- 头部压缩（HPACK）
- 服务器推送

#### 8.1.2 HTTP/3 (RFC 9114)

- 基于QUIC协议
- 内置TLS 1.3
- 0-RTT连接建立
- 连接迁移

### 8.2 RESTful API设计

基于HTTP的API设计原则：

```
资源URI设计:
GET    /users           # 获取用户列表
GET    /users/123       # 获取特定用户
POST   /users           # 创建用户
PUT    /users/123       # 更新用户
PATCH  /users/123       # 部分更新
DELETE /users/123       # 删除用户
```

### 8.3 与后续RFC的关系

| RFC | 主题 | 与RFC 7230关系 |
|-----|------|---------------|
| RFC 5789 | PATCH方法 | 扩展HTTP方法 |
| RFC 6265 | Cookie | Cookie规范更新 |
| RFC 6585 | 额外状态码 | 扩展状态码 |
| RFC 7239 | Forwarded | 代理转发信息 |
| RFC 7540 | HTTP/2 | 下一代HTTP |
| RFC 9114 | HTTP/3 | 基于QUIC的HTTP |

### 8.4 教学与研究价值

1. **协议设计**: 请求-响应模型的经典实现
2. **Web架构**: 理解现代Web基础
3. **API设计**: RESTful架构基础
4. **性能优化**: 缓存、连接管理、压缩

---

## 参考文献

1. Fielding, R., et al. "Hypertext Transfer Protocol -- HTTP/1.1." RFC 2616, June 1999. (Obsoleted by RFC 7230-7235)
2. Fielding, R., and J. Reschke. "Hypertext Transfer Protocol (HTTP/1.1): Message Syntax and Routing." RFC 7230, June 2014.
3. Belshe, M., et al. "Hypertext Transfer Protocol Version 2 (HTTP/2)." RFC 7540, May 2015.
4. Bishop, M. "HTTP/3." RFC 9114, June 2022.

---

_文档版本: 1.0_
_最后更新: 2026年_
_状态: 核心RFC映射完成_
