#!/bin/bash
# FormalScience Refactor - Development Script
# ===========================================

set -e

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
CYAN='\033[0;36m'
NC='\033[0m' # No Color

# Helper functions
log_info() {
    echo -e "${BLUE}[INFO]${NC} $1"
}

log_success() {
    echo -e "${GREEN}[SUCCESS]${NC} $1"
}

log_warning() {
    echo -e "${YELLOW}[WARNING]${NC} $1"
}

log_error() {
    echo -e "${RED}[ERROR]${NC} $1"
}

log_dev() {
    echo -e "${CYAN}[DEV]${NC} $1"
}

# Default configuration
DOCS_PORT=${DOCS_PORT:-3000}
DOCS_HOST=${DOCS_HOST:-127.0.0.1}
LEAN_DIR="../Concept"
RUST_DIR="../FormalRE"

# Function to check if a port is in use
is_port_in_use() {
    local port=$1
    if command -v lsof >/dev/null 2>&1; then
        lsof -Pi :$port -sTCP:LISTEN -t >/dev/null 2>&1
    elif command -v netstat >/dev/null 2>&1; then
        netstat -tuln 2>/dev/null | grep -q ":$port "
    else
        return 1
    fi
}

# Function to find an available port
find_available_port() {
    local port=$1
    while is_port_in_use $port; do
        port=$((port + 1))
    done
    echo $port
}

# Function to cleanup on exit
cleanup() {
    log_info "Shutting down development server..."
    
    # Kill background processes
    if [ -n "$LEAN_PID" ]; then
        kill $LEAN_PID 2>/dev/null || true
    fi
    if [ -n "$RUST_PID" ]; then
        kill $RUST_PID 2>/dev/null || true
    fi
    if [ -n "$DOCS_PID" ]; then
        kill $DOCS_PID 2>/dev/null || true
    fi
    
    log_success "Development server stopped"
    exit 0
}

# Trap signals for cleanup
trap cleanup SIGINT SIGTERM EXIT

# Print banner
print_banner() {
    clear
    echo ""
    echo -e "${CYAN}╔══════════════════════════════════════════════════════════════╗${NC}"
    echo -e "${CYAN}║${NC}           ${GREEN}FormalScience Development Server${NC}                  ${CYAN}║${NC}"
    echo -e "${CYAN}╚══════════════════════════════════════════════════════════════╝${NC}"
    echo ""
}

# Show help
show_help() {
    echo "FormalScience Development Script"
    echo ""
    echo "Usage: $0 [options] [command]"
    echo ""
    echo "Commands:"
    echo "  all         Start all development services (default)"
    echo "  docs        Start documentation server only"
    echo "  lean        Watch and rebuild Lean project"
    echo "  rust        Watch and rebuild Rust project"
    echo "  python      Watch Python files for changes"
    echo "  help        Show this help message"
    echo ""
    echo "Options:"
    echo "  -p, --port PORT     Set documentation server port (default: 3000)"
    echo "  -h, --host HOST     Set documentation server host (default: 127.0.0.1)"
    echo "  --no-lean           Skip Lean build"
    echo "  --no-rust           Skip Rust build"
    echo "  --no-docs           Skip documentation server"
    echo ""
    echo "Examples:"
    echo "  $0                  Start all services"
    echo "  $0 docs             Start documentation server only"
    echo "  $0 -p 8080          Start all services on port 8080"
    echo "  $0 all --no-rust    Start all services except Rust"
    echo ""
}

# Start documentation server
start_docs() {
    log_dev "Starting documentation server..."
    
    # Check for available port
    if is_port_in_use $DOCS_PORT; then
        local new_port=$(find_available_port $DOCS_PORT)
        log_warning "Port $DOCS_PORT is in use, using port $new_port instead"
        DOCS_PORT=$new_port
    fi
    
    # Check if mdBook is available
    if command -v mdbook >/dev/null 2>&1; then
        log_info "Using mdBook for documentation"
        mdbook serve ./docs -p $DOCS_PORT -n $DOCS_HOST &
        DOCS_PID=$!
    elif [ -d "./docs" ] && [ -f "./docs/book.toml" ]; then
        log_info "Using npx mdBook for documentation"
        npx mdbook serve ./docs -p $DOCS_PORT -n $DOCS_HOST &
        DOCS_PID=$!
    elif command -v python3 >/dev/null 2>&1 || command -v python >/dev/null 2>&1; then
        log_info "Using Python HTTP server for documentation"
        local python_cmd=$(command -v python3 || command -v python)
        cd ./docs && $python_cmd -m http.server $DOCS_PORT --bind $DOCS_HOST &
        DOCS_PID=$!
        cd - > /dev/null
    else
        log_warning "No documentation server available"
        return 1
    fi
    
    log_success "Documentation server running at http://$DOCS_HOST:$DOCS_PORT"
    
    # Wait a moment for server to start
    sleep 2
}

# Watch Lean project
watch_lean() {
    log_dev "Starting Lean watcher..."
    
    if ! command -v lake >/dev/null 2>&1; then
        log_warning "Lake not found, skipping Lean watcher"
        return 1
    fi
    
    if [ ! -d "$LEAN_DIR" ]; then
        log_warning "Lean directory not found: $LEAN_DIR"
        return 1
    fi
    
    log_info "Watching Lean project at $LEAN_DIR"
    
    # Start initial build
    (cd "$LEAN_DIR" && lake build) || log_warning "Initial Lean build failed"
    
    # Watch for changes and rebuild
    (
        cd "$LEAN_DIR"
        while true; do
            # Use fswatch or inotifywait if available, otherwise use simple polling
            if command -v fswatch >/dev/null 2>&1; then
                fswatch -o -r . --include ".*\\.lean$" 2>/dev/null | while read; do
                    log_info "Lean file changed, rebuilding..."
                    lake build 2>&1 | tail -20
                done
            elif command -v inotifywait >/dev/null 2>&1; then
                inotifywait -e modify -r . --include ".*\\.lean$" 2>/dev/null | while read; do
                    log_info "Lean file changed, rebuilding..."
                    lake build 2>&1 | tail -20
                done
            else
                # Fallback: rebuild every 30 seconds if files changed
                sleep 30
                if find . -name "*.lean" -newer .lake 2>/dev/null | grep -q .; then
                    log_info "Lean files changed, rebuilding..."
                    lake build 2>&1 | tail -20
                fi
            fi
        done
    ) &
    
    LEAN_PID=$!
    log_success "Lean watcher started (PID: $LEAN_PID)"
}

# Watch Rust project
watch_rust() {
    log_dev "Starting Rust watcher..."
    
    if ! command -v cargo >/dev/null 2>&1; then
        log_warning "Cargo not found, skipping Rust watcher"
        return 1
    fi
    
    if [ ! -d "$RUST_DIR" ]; then
        log_warning "Rust directory not found: $RUST_DIR"
        return 1
    fi
    
    log_info "Watching Rust project at $RUST_DIR"
    
    # Use cargo-watch if available
    if command -v cargo-watch >/dev/null 2>&1; then
        (cd "$RUST_DIR" && cargo watch -x build -x test) &
        RUST_PID=$!
        log_success "Rust watcher started with cargo-watch (PID: $RUST_PID)"
    else
        # Fallback: manual watching
        (
            cd "$RUST_DIR"
            cargo build 2>&1 || log_warning "Initial Rust build failed"
            
            while true; do
                sleep 10
                if find . -name "*.rs" -newer target 2>/dev/null | grep -q .; then
                    log_info "Rust files changed, rebuilding..."
                    cargo build 2>&1 | tail -20
                fi
            done
        ) &
        
        RUST_PID=$!
        log_success "Rust watcher started (PID: $RUST_PID)"
        log_info "Tip: Install cargo-watch for better experience: cargo install cargo-watch"
    fi
}

# Watch Python files
watch_python() {
    log_dev "Starting Python watcher..."
    
    local python_cmd=""
    if command -v python3 >/dev/null 2>&1; then
        python_cmd="python3"
    elif command -v python >/dev/null 2>&1; then
        python_cmd="python"
    else
        log_warning "Python not found, skipping Python watcher"
        return 1
    fi
    
    if [ ! -d "../Composed" ]; then
        log_warning "Python directory not found: ../Composed"
        return 1
    fi
    
    log_info "Watching Python files at ../Composed"
    
    (
        cd ../Composed
        while true; do
            sleep 15
            if find . -name "*.py" -mtime -0.1 2>/dev/null | grep -q .; then
                log_info "Python files changed, checking syntax..."
                $python_cmd -m py_compile $(find . -name "*.py" -mtime -0.1) 2>&1 | tail -10
            fi
        done
    ) &
    
    PYTHON_PID=$!
    log_success "Python watcher started (PID: $PYTHON_PID)"
}

# Watch documentation files
watch_docs() {
    log_dev "Starting documentation file watcher..."
    
    if [ ! -d "./docs" ]; then
        log_warning "Documentation directory not found: ./docs"
        return 1
    fi
    
    log_info "Watching documentation files..."
    
    (
        cd ./docs
        while true; do
            if command -v fswatch >/dev/null 2>&1; then
                fswatch -o -r . 2>/dev/null | while read; do
                    log_info "Documentation files changed, rebuilding..."
                    if command -v mdbook >/dev/null 2>&1; then
                        mdbook build
                    fi
                done
            else
                sleep 30
                if find . -name "*.md" -mtime -0.1 2>/dev/null | grep -q .; then
                    log_info "Markdown files changed, rebuilding..."
                    if command -v mdbook >/dev/null 2>&1; then
                        mdbook build
                    fi
                fi
            fi
        done
    ) &
    
    log_success "Documentation watcher started"
}

# Print status
print_status() {
    echo ""
    echo -e "${GREEN}═══════════════════════════════════════════════════════${NC}"
    echo -e "${GREEN}  Development server is running!${NC}"
    echo -e "${GREEN}═══════════════════════════════════════════════════════${NC}"
    echo ""
    
    if [ -n "$DOCS_PID" ]; then
        echo -e "  ${CYAN}📚 Documentation:${NC} http://$DOCS_HOST:$DOCS_PORT"
    fi
    if [ -n "$LEAN_PID" ]; then
        echo -e "  ${CYAN}🔷 Lean:${NC} Watching ../Concept"
    fi
    if [ -n "$RUST_PID" ]; then
        echo -e "  ${CYAN}🦀 Rust:${NC} Watching ../FormalRE"
    fi
    if [ -n "$PYTHON_PID" ]; then
        echo -e "  ${CYAN}🐍 Python:${NC} Watching ../Composed"
    fi
    
    echo ""
    echo -e "  ${YELLOW}Press Ctrl+C to stop all services${NC}"
    echo ""
}

# Main function
main() {
    # Default values
    CMD="all"
    ENABLE_LEAN=true
    ENABLE_RUST=true
    ENABLE_DOCS=true
    
    # Parse arguments
    while [[ $# -gt 0 ]]; do
        case $1 in
            -p|--port)
                DOCS_PORT="$2"
                shift 2
                ;;
            -h|--host)
                DOCS_HOST="$2"
                shift 2
                ;;
            --no-lean)
                ENABLE_LEAN=false
                shift
                ;;
            --no-rust)
                ENABLE_RUST=false
                shift
                ;;
            --no-docs)
                ENABLE_DOCS=false
                shift
                ;;
            help|--help|-h)
                show_help
                exit 0
                ;;
            all|docs|lean|rust|python)
                CMD="$1"
                shift
                ;;
            *)
                log_error "Unknown option: $1"
                show_help
                exit 1
                ;;
        esac
    done
    
    print_banner
    
    # Execute based on command
    case $CMD in
        all)
            log_info "Starting all development services..."
            $ENABLE_DOCS && start_docs || true
            $ENABLE_LEAN && watch_lean || true
            $ENABLE_RUST && watch_rust || true
            watch_python || true
            watch_docs || true
            print_status
            ;;
        docs)
            log_info "Starting documentation server only..."
            start_docs
            echo -e "  ${YELLOW}Press Ctrl+C to stop${NC}"
            ;;
        lean)
            log_info "Starting Lean watcher only..."
            watch_lean
            echo -e "  ${YELLOW}Press Ctrl+C to stop${NC}"
            ;;
        rust)
            log_info "Starting Rust watcher only..."
            watch_rust
            echo -e "  ${YELLOW}Press Ctrl+C to stop${NC}"
            ;;
        python)
            log_info "Starting Python watcher only..."
            watch_python
            echo -e "  ${YELLOW}Press Ctrl+C to stop${NC}"
            ;;
    esac
    
    # Wait for all background processes
    wait
}

# Run main function
main "$@"
