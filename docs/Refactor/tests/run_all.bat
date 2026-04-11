@echo off
REM FormalScience 一键测试脚本 (Windows)
REM 
REM 功能: 运行所有测试并生成综合报告
REM 
REM 使用方法:
REM   run_all.bat [options]
REM 
REM 选项:
REM   --lean-only     只运行 Lean 测试
REM   --rust-only     只运行 Rust 测试
REM   --md-only       只运行 Markdown 验证
REM   --coverage      生成覆盖率报告
REM   --ci            CI 模式 (非交互式)

setlocal EnableDelayedExpansion

REM 设置代码页为 UTF-8
chcp 65001 >nul 2>&1

REM 脚本目录
set "SCRIPT_DIR=%~dp0"
set "TESTS_DIR=%SCRIPT_DIR%"
for %%I in ("%SCRIPT_DIR%..\..\..") do set "PROJECT_ROOT=%%~fI"

REM 计数器
set "TESTS_PASSED=0"
set "TESTS_FAILED=0"

REM 解析参数
set "LEAN_ONLY=false"
set "RUST_ONLY=false"
set "MD_ONLY=false"
set "GENERATE_COVERAGE=false"
set "CI_MODE=false"

:parse_args
if "%~1"=="" goto :done_parse
if "%~1"=="--lean-only" (
    set "LEAN_ONLY=true"
    shift
    goto :parse_args
)
if "%~1"=="--rust-only" (
    set "RUST_ONLY=true"
    shift
    goto :parse_args
)
if "%~1"=="--md-only" (
    set "MD_ONLY=true"
    shift
    goto :parse_args
)
if "%~1"=="--coverage" (
    set "GENERATE_COVERAGE=true"
    shift
    goto :parse_args
)
if "%~1"=="--ci" (
    set "CI_MODE=true"
    shift
    goto :parse_args
)
if "%~1"=="--help" goto :show_help
if "%~1"=="-h" goto :show_help
echo 未知选项: %~1
goto :error

:show_help
echo FormalScience 测试脚本
echo.
echo 选项:
echo   --lean-only     只运行 Lean 测试
echo   --rust-only     只运行 Rust 测试
echo   --md-only       只运行 Markdown 验证
echo   --coverage      生成覆盖率报告
echo   --ci            CI 模式 (非交互式)
echo   --help, -h      显示帮助
goto :end

:done_parse

REM 确定运行哪些测试
set "RUN_LEAN=true"
set "RUN_RUST=true"
set "RUN_MD=true"

if "%LEAN_ONLY%"=="true" (
    set "RUN_RUST=false"
    set "RUN_MD=false"
)

if "%RUST_ONLY%"=="true" (
    set "RUN_LEAN=false"
    set "RUN_MD=false"
)

if "%MD_ONLY%"=="true" (
    set "RUN_LEAN=false"
    set "RUN_RUST=false"
)

REM 打印标题
echo.
echo ╔══════════════════════════════════════════════════════════╗
echo ║       FormalScience 综合测试套件                        ║
echo ╚══════════════════════════════════════════════════════════╝
echo.
echo 项目路径: %PROJECT_ROOT%
echo 测试路径: %TESTS_DIR%
echo 运行时间: %date% %time%
echo.

REM 检查依赖
echo 📋 检查依赖...
echo.

if "%RUN_LEAN%"=="true" (
    lean --version >nul 2>&1
    if errorlevel 1 (
        echo ⚠️  Lean 未安装
        set "RUN_LEAN=false"
    ) else (
        echo ✅ Lean 已安装
    )
)

if "%RUN_RUST%"=="true" (
    cargo --version >nul 2>&1
    if errorlevel 1 (
        echo ⚠️  Rust/Cargo 未安装
        set "RUN_RUST=false"
    ) else (
        echo ✅ Rust/Cargo 已安装
    )
)

if "%RUN_MD%"=="true" (
    python --version >nul 2>&1
    if errorlevel 1 (
        python3 --version >nul 2>&1
        if errorlevel 1 (
            echo ⚠️  Python 未安装
            set "RUN_MD=false"
        ) else (
            echo ✅ Python3 已安装
            set "PYTHON_CMD=python3"
        )
    ) else (
        echo ✅ Python 已安装
        set "PYTHON_CMD=python"
    )
)

echo.

REM 记录开始时间
set "START_TIME=%time%"

REM Lean 测试
if "%RUN_LEAN%"=="true" (
    echo ══════════════════════════════════════════════════════════
    echo                   Lean 测试
    echo ══════════════════════════════════════════════════════════
    echo.
    
    cd /d "%TESTS_DIR%"
    
    if exist "lean_tests.lean" (
        echo ▶ 运行: Lean 测试套件
        echo   命令: lean --run lean_tests.lean
        echo.
        
        lean --run lean_tests.lean
        if !errorlevel! equ 0 (
            echo ✅ Lean 测试套件 通过
            set /a TESTS_PASSED+=1
        ) else (
            echo ❌ Lean 测试套件 失败
            set /a TESTS_FAILED+=1
        )
    ) else (
        echo ⚠️  lean_tests.lean 不存在
    )
    
    echo.
    
    REM 验证示例文件
    set "LEAN_EXAMPLES=%PROJECT_ROOT%\docs\Refactor\examples\lean"
    if exist "!LEAN_EXAMPLES!" (
        echo 验证 Lean 示例文件...
        for %%F in ("!LEAN_EXAMPLES!\*.lean") do (
            echo   检查 %%~nF... 
            lean "%%F" >nul 2>&1
            if !errorlevel! equ 0 (
                echo     ✓
            ) else (
                echo     ⚠
            )
        )
    )
    
    echo.
)

REM Rust 测试
if "%RUN_RUST%"=="true" (
    echo ══════════════════════════════════════════════════════════
    echo                   Rust 测试
    echo ══════════════════════════════════════════════════════════
    echo.
    
    cd /d "%TESTS_DIR%"
    
    if exist "Cargo.toml" (
        echo ▶ 运行: Rust 单元测试
        echo   命令: cargo test --lib
        echo.
        
        cargo test --lib
        if !errorlevel! equ 0 (
            echo ✅ Rust 单元测试 通过
            set /a TESTS_PASSED+=1
        ) else (
            echo ❌ Rust 单元测试 失败
            set /a TESTS_FAILED+=1
        )
        
        echo.
        echo ▶ 运行: Rust 文档测试
        echo   命令: cargo test --doc
        echo.
        
        cargo test --doc
        if !errorlevel! equ 0 (
            echo ✅ Rust 文档测试 通过
            set /a TESTS_PASSED+=1
        ) else (
            echo ❌ Rust 文档测试 失败
            set /a TESTS_FAILED+=1
        )
    ) else (
        if exist "rust_tests.rs" (
            echo ⚠️  未找到 Cargo.toml，跳过 Rust 测试
        ) else (
            echo ⚠️  rust_tests.rs 不存在
        )
    )
    
    echo.
    
    REM 验证示例文件
    set "RUST_EXAMPLES=%PROJECT_ROOT%\docs\Refactor\examples\rust"
    if exist "!RUST_EXAMPLES!" (
        echo 验证 Rust 示例文件...
        for %%F in ("!RUST_EXAMPLES!\*.rs") do (
            echo   检查 %%~nF... 
            rustc --edition 2021 --emit=metadata "%%F" >nul 2>&1
            if !errorlevel! equ 0 (
                echo     ✓
            ) else (
                echo     ⚠
            )
        )
    )
    
    echo.
)

REM Markdown 验证
if "%RUN_MD%"=="true" (
    echo ══════════════════════════════════════════════════════════
    echo                   Markdown 验证
    echo ══════════════════════════════════════════════════════════
    echo.
    
    cd /d "%TESTS_DIR%"
    
    if exist "validate_md.py" (
        echo ▶ 运行: Markdown 格式验证
        echo   命令: %PYTHON_CMD% validate_md.py --path "%PROJECT_ROOT%\docs"
        echo.
        
        %PYTHON_CMD% validate_md.py --path "%PROJECT_ROOT%\docs"
        if !errorlevel! equ 0 (
            echo ✅ Markdown 格式验证 通过
            set /a TESTS_PASSED+=1
        ) else (
            echo ❌ Markdown 格式验证 失败
            set /a TESTS_FAILED+=1
        )
    ) else (
        echo ⚠️  validate_md.py 不存在
    )
    
    echo.
)

REM 覆盖率报告
if "%GENERATE_COVERAGE%"=="true" (
    echo ══════════════════════════════════════════════════════════
    echo                   覆盖率报告
    echo ══════════════════════════════════════════════════════════
    echo.
    
    cd /d "%TESTS_DIR%"
    
    if exist "coverage_report.py" (
        set "OUTPUT_DIR=%TESTS_DIR%\coverage_output"
        if not exist "!OUTPUT_DIR!" mkdir "!OUTPUT_DIR!"
        
        echo ▶ 生成: 覆盖率报告
        echo   命令: %PYTHON_CMD% coverage_report.py --output "!OUTPUT_DIR!"
        echo.
        
        %PYTHON_CMD% coverage_report.py --output "!OUTPUT_DIR!"
        if !errorlevel! equ 0 (
            echo ✅ 覆盖率报告 生成成功
            set /a TESTS_PASSED+=1
            
            if exist "!OUTPUT_DIR!\index.html" (
                echo.
                echo 📊 覆盖率报告: !OUTPUT_DIR!\index.html
            )
        ) else (
            echo ❌ 覆盖率报告 生成失败
            set /a TESTS_FAILED+=1
        )
    ) else (
        echo ⚠️  coverage_report.py 不存在
    )
    
    echo.
)

REM 记录结束时间
set "END_TIME=%time%"

REM 生成综合报告
echo.
echo ╔══════════════════════════════════════════════════════════╗
echo ║                  测试结果汇总                            ║
echo ╚══════════════════════════════════════════════════════════╝
echo.

echo 统计信息:
echo   ✅ 通过: %TESTS_PASSED%
echo   ❌ 失败: %TESTS_FAILED%
set /a TOTAL=TESTS_PASSED+TESTS_FAILED
echo   📊 总计: %TOTAL%

if %TOTAL% gtr 0 (
    set /a PASS_RATE=TESTS_PASSED*100/TOTAL
    echo   📈 通过率: !PASS_RATE!%%
)

echo.
echo 时间信息:
echo   开始: %START_TIME%
echo   结束: %END_TIME%

echo.
if %TESTS_FAILED% equ 0 (
    echo ╔══════════════════════════════════════════════════════════╗
    echo ║              🎉 所有测试通过!                            ║
    echo ╚══════════════════════════════════════════════════════════╝
    goto :success
) else (
    echo ╔══════════════════════════════════════════════════════════╗
    echo ║              ⚠️  部分测试失败                            ║
    echo ╚══════════════════════════════════════════════════════════╝
    goto :error
)

:success
exit /b 0

:error
exit /b 1

:end
exit /b 0
