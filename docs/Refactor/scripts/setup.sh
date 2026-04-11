#!/bin/bash
# FormalScience Refactor - Environment Setup Script
# =================================================

set -e

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
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

# Check if command exists
command_exists() {
    command -v "$1" >/dev/null 2>&1
}

# Print header
print_header() {
    echo ""
    echo "========================================"
    echo "  FormalScience Environment Setup"
    echo "========================================"
    echo ""
}

# Check system requirements
check_system() {
    log_info "Checking system requirements..."
    
    # Check OS
    if [[ "$OSTYPE" == "linux-gnu"* ]]; then
        OS="Linux"
    elif [[ "$OSTYPE" == "darwin"* ]]; then
        OS="macOS"
    elif [[ "$OSTYPE" == "msys" ]] || [[ "$OSTYPE" == "cygwin" ]] || [[ "$OSTYPE" == "win32" ]]; then
        OS="Windows"
    else
        OS="Unknown"
    fi
    
    log_info "Detected OS: $OS"
}

# Check and install Node.js
check_nodejs() {
    log_info "Checking Node.js installation..."
    
    if command_exists node; then
        NODE_VERSION=$(node --version | cut -d'v' -f2)
        log_success "Node.js found: v$NODE_VERSION"
        
        # Check version >= 18
        REQUIRED_VERSION="18.0.0"
        if [ "$(printf '%s\n' "$REQUIRED_VERSION" "$NODE_VERSION" | sort -V | head -n1)" = "$REQUIRED_VERSION" ]; then
            log_success "Node.js version is compatible (>= 18.0.0)"
        else
            log_warning "Node.js version is too old. Please upgrade to 18.0.0 or later"
            log_info "Visit: https://nodejs.org/"
        fi
    else
        log_error "Node.js not found"
        log_info "Please install Node.js 18.0.0 or later from https://nodejs.org/"
        exit 1
    fi
    
    # Check npm
    if command_exists npm; then
        NPM_VERSION=$(npm --version)
        log_success "npm found: v$NPM_VERSION"
    else
        log_error "npm not found"
        exit 1
    fi
}

# Check Lean 4
check_lean() {
    log_info "Checking Lean 4 installation..."
    
    if command_exists lean; then
        LEAN_VERSION=$(lean --version 2>/dev/null || echo "unknown")
        log_success "Lean found: $LEAN_VERSION"
        
        # Check lake
        if command_exists lake; then
            log_success "Lake (Lean build tool) found"
        else
            log_warning "Lake not found. Lean may not be properly installed"
        fi
    else
        log_warning "Lean 4 not found"
        log_info "To install Lean 4, visit: https://leanprover-community.github.io/get_started.html"
        log_info "Or run: curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh"
    fi
}

# Check Rust
check_rust() {
    log_info "Checking Rust installation..."
    
    if command_exists rustc; then
        RUST_VERSION=$(rustc --version)
        log_success "Rust found: $RUST_VERSION"
        
        # Check cargo
        if command_exists cargo; then
            CARGO_VERSION=$(cargo --version)
            log_success "Cargo found: $CARGO_VERSION"
        else
            log_warning "Cargo not found. Rust may not be properly installed"
        fi
    else
        log_warning "Rust not found"
        log_info "To install Rust, visit: https://rustup.rs/"
        log_info "Or run: curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh"
    fi
}

# Check Python
check_python() {
    log_info "Checking Python installation..."
    
    # Check for python3 first, then python
    if command_exists python3; then
        PYTHON_CMD="python3"
    elif command_exists python; then
        PYTHON_CMD="python"
    else
        PYTHON_CMD=""
    fi
    
    if [ -n "$PYTHON_CMD" ]; then
        PYTHON_VERSION=$($PYTHON_CMD --version 2>&1)
        log_success "Python found: $PYTHON_VERSION"
        
        # Check pip
        if command_exists pip || command_exists pip3; then
            log_success "pip found"
        else
            log_warning "pip not found"
        fi
    else
        log_warning "Python not found"
        log_info "Please install Python 3.8 or later from https://www.python.org/"
    fi
}

# Check Git
check_git() {
    log_info "Checking Git installation..."
    
    if command_exists git; then
        GIT_VERSION=$(git --version)
        log_success "Git found: $GIT_VERSION"
    else
        log_warning "Git not found"
        log_info "Please install Git from https://git-scm.com/"
    fi
}

# Install Node.js dependencies
install_node_deps() {
    log_info "Installing Node.js dependencies..."
    
    if [ -f "package.json" ]; then
        npm install
        log_success "Node.js dependencies installed"
    else
        log_warning "package.json not found. Skipping Node.js dependencies installation"
    fi
}

# Install Python dependencies
install_python_deps() {
    log_info "Checking Python dependencies..."
    
    if [ -f "requirements.txt" ]; then
        if command_exists pip; then
            pip install -r requirements.txt
            log_success "Python dependencies installed"
        elif command_exists pip3; then
            pip3 install -r requirements.txt
            log_success "Python dependencies installed"
        else
            log_warning "pip not found. Cannot install Python dependencies"
        fi
    else
        log_info "requirements.txt not found. Skipping Python dependencies installation"
    fi
}

# Install Lean dependencies
install_lean_deps() {
    log_info "Checking Lean dependencies..."
    
    if [ -d "../Concept" ]; then
        if command_exists lake; then
            cd ../Concept && lake update
            cd - > /dev/null
            log_success "Lean dependencies updated"
        fi
    fi
}

# Install Rust dependencies
install_rust_deps() {
    log_info "Checking Rust dependencies..."
    
    if [ -d "../FormalRE" ]; then
        if command_exists cargo; then
            cd ../FormalRE && cargo fetch
            cd - > /dev/null
            log_success "Rust dependencies fetched"
        fi
    fi
}

# Setup pre-commit hooks
setup_hooks() {
    log_info "Setting up git hooks..."
    
    if [ -d ".git" ]; then
        # Create pre-commit hook
        cat > .git/hooks/pre-commit << 'EOF'
#!/bin/bash
echo "Running pre-commit checks..."

# Run linting
make lint || true

# Check for secrets (basic check)
if grep -r "password\|secret\|token" --include="*.md" --include="*.json" . 2>/dev/null | grep -v "node_modules\|.git\|example\|template"; then
    echo "Warning: Potential secrets found in files"
fi

echo "Pre-commit checks complete"
EOF
        chmod +x .git/hooks/pre-commit
        log_success "Pre-commit hook installed"
    else
        log_warning "Not a git repository. Skipping hooks setup"
    fi
}

# Create environment file
create_env_file() {
    log_info "Creating environment configuration..."
    
    if [ ! -f ".env" ]; then
        cat > .env << 'EOF'
# FormalScience Environment Configuration
# ========================================

# Development settings
NODE_ENV=development
DEBUG=true

# Documentation settings
DOCS_PORT=3000
DOCS_HOST=127.0.0.1

# Build settings
BUILD_DIR=./build
DIST_DIR=./dist

# Lean settings
LEAN_DIR=../Concept

# Rust settings
RUST_DIR=../FormalRE

# Python settings
PYTHON_DIR=../Composed
EOF
        log_success "Environment file created: .env"
    else
        log_info "Environment file already exists: .env"
    fi
}

# Print summary
print_summary() {
    echo ""
    echo "========================================"
    echo "  Setup Complete!"
    echo "========================================"
    echo ""
    echo "Available commands:"
    echo "  make build     - Build all projects"
    echo "  make test      - Run all tests"
    echo "  make docs      - Generate documentation"
    echo "  make serve     - Start development server"
    echo "  make clean     - Clean build artifacts"
    echo "  npm run dev    - Start development mode"
    echo ""
    echo "For more information, see README.md"
    echo ""
}

# Main function
main() {
    print_header
    check_system
    
    echo ""
    echo "--- Checking Dependencies ---"
    check_nodejs
    check_lean
    check_rust
    check_python
    check_git
    
    echo ""
    echo "--- Installing Dependencies ---"
    install_node_deps
    install_python_deps
    install_lean_deps
    install_rust_deps
    
    echo ""
    echo "--- Configuring Environment ---"
    setup_hooks
    create_env_file
    
    print_summary
}

# Run main function
main "$@"
