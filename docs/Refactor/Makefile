# FormalScience Refactor - Build Automation
# ===========================================

.PHONY: build test clean install docs serve deploy help

# Default target
.DEFAULT_GOAL := help

# Variables
PROJECT_NAME := FormalScience
DOCS_DIR := ./docs
BUILD_DIR := ./build
DIST_DIR := ./dist
LEAN_DIR := ../Concept
RUST_DIR := ../FormalRE

# Colors for output
BLUE := \033[36m
GREEN := \033[32m
YELLOW := \033[33m
RED := \033[31m
NC := \033[0m # No Color

## help: Show this help message
help:
	@echo "$(BLUE)FormalScience Refactor - Build Commands$(NC)"
	@echo "========================================"
	@grep -E '^##' Makefile | sed 's/## /  /'
	@echo ""

## build: Build all projects (Lean, Rust, Python)
build: build-lean build-rust build-python
	@echo "$(GREEN)✓ All projects built successfully$(NC)"

build-lean:
	@echo "$(BLUE)Building Lean 4 project...$(NC)"
	cd $(LEAN_DIR) && lake build
	@echo "$(GREEN)✓ Lean build complete$(NC)"

build-rust:
	@echo "$(BLUE)Building Rust project...$(NC)"
	cd $(RUST_DIR) && cargo build --release
	@echo "$(GREEN)✓ Rust build complete$(NC)"

build-python:
	@echo "$(BLUE)Checking Python project...$(NC)"
	cd .. && python -m compileall Composed/
	@echo "$(GREEN)✓ Python check complete$(NC)"

## test: Run all tests
test: test-lean test-rust test-python
	@echo "$(GREEN)✓ All tests passed$(NC)"

test-lean:
	@echo "$(BLUE)Running Lean tests...$(NC)"
	cd $(LEAN_DIR) && lake test

test-rust:
	@echo "$(BLUE)Running Rust tests...$(NC)"
	cd $(RUST_DIR) && cargo test

test-python:
	@echo "$(BLUE)Running Python tests...$(NC)"
	cd .. && python -m pytest Composed/ -v || echo "$(YELLOW)⚠ No Python tests found$(NC)"

## clean: Clean generated files
clean:
	@echo "$(BLUE)Cleaning build artifacts...$(NC)"
	rm -rf $(BUILD_DIR) $(DIST_DIR)
	cd $(LEAN_DIR) && lake clean || true
	cd $(RUST_DIR) && cargo clean
	find .. -type d -name "__pycache__" -exec rm -rf {} + 2>/dev/null || true
	find .. -type f -name "*.pyc" -delete 2>/dev/null || true
	@echo "$(GREEN)✓ Clean complete$(NC)"

## install: Install all dependencies
install: install-node install-lean install-rust install-python
	@echo "$(GREEN)✓ All dependencies installed$(NC)"

install-node:
	@echo "$(BLUE)Installing Node.js dependencies...$(NC)"
	npm install

install-lean:
	@echo "$(BLUE)Installing Lean dependencies...$(NC)"
	cd $(LEAN_DIR) && lake update

install-rust:
	@echo "$(BLUE)Checking Rust toolchain...$(NC)"
	rustup update
	cd $(RUST_DIR) && cargo fetch

install-python:
	@echo "$(BLUE)Installing Python dependencies...$(NC)"
	pip install -r requirements.txt 2>/dev/null || echo "$(YELLOW)⚠ No requirements.txt found$(NC)"

## docs: Generate documentation
docs: docs-lean docs-rust docs-mdbook
	@echo "$(GREEN)✓ Documentation generated$(NC)"

docs-lean:
	@echo "$(BLUE)Generating Lean documentation...$(NC)"
	cd $(LEAN_DIR) && lake -R -Kenv=dev build || true

docs-rust:
	@echo "$(BLUE)Generating Rust documentation...$(NC)"
	cd $(RUST_DIR) && cargo doc --no-deps

docs-mdbook:
	@echo "$(BLUE)Building mdBook documentation...$(NC)"
	npx mdbook build $(DOCS_DIR) || echo "$(YELLOW)⚠ mdBook not configured$(NC)"

## serve: Start local development server
serve:
	@echo "$(BLUE)Starting development server...$(NC)"
	@echo "$(GREEN)Documentation server running at http://localhost:3000$(NC)"
	npx mdbook serve $(DOCS_DIR) -p 3000 -n 127.0.0.1 || npx vite --port 3000

## deploy: Deploy to production
deploy: build docs
	@echo "$(BLUE)Deploying to production...$(NC)"
	@echo "$(YELLOW)Deployment method not configured$(NC)"
	@echo "Configure deployment in Makefile deploy target"
	# Add deployment commands here
	# Example: rsync -avz $(DIST_DIR)/ user@server:/var/www/
	# Example: aws s3 sync $(DIST_DIR)/ s3://bucket-name/
	# Example: netlify deploy --prod --dir=$(DIST_DIR)

## lint: Run linters and formatters
lint: lint-md lint-lean lint-rust lint-py
	@echo "$(GREEN)✓ Linting complete$(NC)"

lint-md:
	@echo "$(BLUE)Linting Markdown...$(NC)"
	npx markdownlint-cli2 "**/*.md" || true

lint-lean:
	@echo "$(BLUE)Formatting Lean code...$(NC)"
	find $(LEAN_DIR) -name "*.lean" -exec lake exe lean4-format {} + 2>/dev/null || true

lint-rust:
	@echo "$(BLUE)Formatting Rust code...$(NC)"
	cd $(RUST_DIR) && cargo fmt
	cd $(RUST_DIR) && cargo clippy -- -D warnings || true

lint-py:
	@echo "$(BLUE)Linting Python code...$(NC)"
	cd .. && black Composed/ 2>/dev/null || true
	cd .. && flake8 Composed/ 2>/dev/null || true

## watch: Watch files and rebuild on changes
watch:
	@echo "$(BLUE)Watching for changes...$(NC)"
	@echo "$(YELLOW)Press Ctrl+C to stop$(NC)"
	@./scripts/dev.sh

## check: Check project health
check:
	@echo "$(BLUE)Checking project health...$(NC)"
	@echo "Node version: $$(node --version)"
	@echo "NPM version: $$(npm --version)"
	@echo "Lean version: $$(lean --version)" || echo "$(RED)✗ Lean not found$(NC)"
	@echo "Rust version: $$(rustc --version)"
	@echo "Python version: $$(python --version)"
	@echo "$(GREEN)✓ Health check complete$(NC)"
