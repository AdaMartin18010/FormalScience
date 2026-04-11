#!/usr/bin/env bash

# =============================================================================
# Release Script for FormalScience Project
# =============================================================================
# This script handles version management, packaging, and changelog generation
# for the FormalScience project.
#
# Usage:
#   ./scripts/release.sh [major|minor|patch] [--dry-run]
#   ./scripts/release.sh --version 1.2.3 [--dry-run]
#   ./scripts/release.sh --changelog-only
#
# =============================================================================

set -euo pipefail

# Configuration
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
PACKAGE_NAME="formal-science"
REPO_URL="https://github.com/${GITHUB_REPOSITORY:-user/repo}"

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Default values
VERSION_BUMP=""
SPECIFIED_VERSION=""
DRY_RUN=false
CHANGELOG_ONLY=false
SKIP_CONFIRM=false

# =============================================================================
# Helper Functions
# =============================================================================

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

usage() {
    cat << EOF
Usage: $(basename "$0") [OPTIONS] [major|minor|patch]

Options:
    -v, --version VERSION   Specify exact version (e.g., 1.2.3)
    -d, --dry-run          Show what would be done without making changes
    -c, --changelog-only   Only generate changelog, don't create release
    -y, --yes              Skip confirmation prompts
    -h, --help             Show this help message

Examples:
    $(basename "$0") patch                    # Bump patch version
    $(basename "$0") minor --dry-run          # Preview minor version bump
    $(basename "$0") --version 2.0.0          # Set specific version
    $(basename "$0") --changelog-only         # Generate changelog only
EOF
}

parse_args() {
    while [[ $# -gt 0 ]]; do
        case $1 in
            -v|--version)
                SPECIFIED_VERSION="$2"
                shift 2
                ;;
            -d|--dry-run)
                DRY_RUN=true
                shift
                ;;
            -c|--changelog-only)
                CHANGELOG_ONLY=true
                shift
                ;;
            -y|--yes)
                SKIP_CONFIRM=true
                shift
                ;;
            -h|--help)
                usage
                exit 0
                ;;
            major|minor|patch)
                VERSION_BUMP="$1"
                shift
                ;;
            *)
                log_error "Unknown option: $1"
                usage
                exit 1
                ;;
        esac
    done

    if [[ -z "$VERSION_BUMP" && -z "$SPECIFIED_VERSION" && "$CHANGELOG_ONLY" == false ]]; then
        log_error "Either specify version bump type (major/minor/patch) or use --version"
        usage
        exit 1
    fi
}

# =============================================================================
# Version Management Functions
# =============================================================================

get_current_version() {
    local version=""
    
    # Try to get version from Cargo.toml
    if [[ -f "${PROJECT_ROOT}/Cargo.toml" ]]; then
        version=$(grep -m 1 '^version' "${PROJECT_ROOT}/Cargo.toml" | cut -d'"' -f2)
    fi
    
    # Try to get version from package.json
    if [[ -z "$version" && -f "${PROJECT_ROOT}/package.json" ]]; then
        version=$(grep -m 1 '"version"' "${PROJECT_ROOT}/package.json" | cut -d'"' -f4)
    fi
    
    # Try to get version from pyproject.toml
    if [[ -z "$version" && -f "${PROJECT_ROOT}/pyproject.toml" ]]; then
        version=$(grep -m 1 '^version' "${PROJECT_ROOT}/pyproject.toml" | cut -d'"' -f2)
    fi
    
    # Try to get version from git tags
    if [[ -z "$version" ]]; then
        version=$(git describe --tags --abbrev=0 2>/dev/null | sed 's/^v//' || echo "0.0.0")
    fi
    
    echo "$version"
}

bump_version() {
    local current_version="$1"
    local bump_type="$2"
    
    # Parse current version
    local major=$(echo "$current_version" | cut -d. -f1)
    local minor=$(echo "$current_version" | cut -d. -f2)
    local patch=$(echo "$current_version" | cut -d. -f3 | cut -d- -f1)
    
    # Apply bump
    case "$bump_type" in
        major)
            major=$((major + 1))
            minor=0
            patch=0
            ;;
        minor)
            minor=$((minor + 1))
            patch=0
            ;;
        patch)
            patch=$((patch + 1))
            ;;
    esac
    
    echo "${major}.${minor}.${patch}"
}

update_version_in_files() {
    local new_version="$1"
    
    log_info "Updating version to $new_version in project files..."
    
    # Update Cargo.toml
    if [[ -f "${PROJECT_ROOT}/Cargo.toml" ]]; then
        if [[ "$DRY_RUN" == false ]]; then
            sed -i.bak "s/^version = \"[^\"]*\"/version = \"$new_version\"/" "${PROJECT_ROOT}/Cargo.toml"
            rm -f "${PROJECT_ROOT}/Cargo.toml.bak"
        fi
        log_success "Updated Cargo.toml"
    fi
    
    # Update package.json
    if [[ -f "${PROJECT_ROOT}/package.json" ]]; then
        if [[ "$DRY_RUN" == false ]]; then
            sed -i.bak "s/\"version\": \"[^\"]*\"/\"version\": \"$new_version\"/" "${PROJECT_ROOT}/package.json"
            rm -f "${PROJECT_ROOT}/package.json.bak"
        fi
        log_success "Updated package.json"
    fi
    
    # Update pyproject.toml
    if [[ -f "${PROJECT_ROOT}/pyproject.toml" ]]; then
        if [[ "$DRY_RUN" == false ]]; then
            sed -i.bak "s/^version = \"[^\"]*\"/version = \"$new_version\"/" "${PROJECT_ROOT}/pyproject.toml"
            rm -f "${PROJECT_ROOT}/pyproject.toml.bak"
        fi
        log_success "Updated pyproject.toml"
    fi
    
    # Update version file
    if [[ "$DRY_RUN" == false ]]; then
        echo "$new_version" > "${PROJECT_ROOT}/VERSION"
    fi
}

# =============================================================================
# Changelog Generation Functions
# =============================================================================

generate_changelog() {
    local new_version="$1"
    local changelog_file="${PROJECT_ROOT}/CHANGELOG.md"
    local temp_file=$(mktemp)
    
    log_info "Generating changelog..."
    
    # Get the last tag
    local last_tag=$(git describe --tags --abbrev=0 2>/dev/null || echo "")
    
    # Generate header
    cat > "$temp_file" << EOF
# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [${new_version}] - $(date +%Y-%m-%d)

EOF

    # Categorize commits
    local features=""
    local fixes=""
    local docs=""
    local refactor=""
    local tests=""
    local other=""
    
    # Get commits since last tag
    local commit_range="HEAD"
    if [[ -n "$last_tag" ]]; then
        commit_range="${last_tag}..HEAD"
    fi
    
    while IFS= read -r line; do
        local hash=$(echo "$line" | cut -d'|' -f1)
        local message=$(echo "$line" | cut -d'|' -f2-)
        
        if [[ "$message" =~ ^feat|feature: ]]; then
            features="${features}- ${message#*: } (${hash:0:7})\n"
        elif [[ "$message" =~ ^fix|bugfix: ]]; then
            fixes="${fixes}- ${message#*: } (${hash:0:7})\n"
        elif [[ "$message" =~ ^docs: ]]; then
            docs="${docs}- ${message#*: } (${hash:0:7})\n"
        elif [[ "$message" =~ ^refactor: ]]; then
            refactor="${refactor}- ${message#*: } (${hash:0:7})\n"
        elif [[ "$message" =~ ^test|tests: ]]; then
            tests="${tests}- ${message#*: } (${hash:0:7})\n"
        else
            other="${other}- ${message} (${hash:0:7})\n"
        fi
    done < <(git log "$commit_range" --pretty=format:"%h|%s")
    
    # Write categorized changes
    if [[ -n "$features" ]]; then
        echo "### Added" >> "$temp_file"
        echo "" >> "$temp_file"
        echo -e "$features" >> "$temp_file"
    fi
    
    if [[ -n "$fixes" ]]; then
        echo "### Fixed" >> "$temp_file"
        echo "" >> "$temp_file"
        echo -e "$fixes" >> "$temp_file"
    fi
    
    if [[ -n "$refactor" ]]; then
        echo "### Changed" >> "$temp_file"
        echo "" >> "$temp_file"
        echo -e "$refactor" >> "$temp_file"
    fi
    
    if [[ -n "$docs" ]]; then
        echo "### Documentation" >> "$temp_file"
        echo "" >> "$temp_file"
        echo -e "$docs" >> "$temp_file"
    fi
    
    if [[ -n "$tests" ]]; then
        echo "### Tests" >> "$temp_file"
        echo "" >> "$temp_file"
        echo -e "$tests" >> "$temp_file"
    fi
    
    if [[ -n "$other" ]]; then
        echo "### Other" >> "$temp_file"
        echo "" >> "$temp_file"
        echo -e "$other" >> "$temp_file"
    fi
    
    # Append existing changelog if it exists
    if [[ -f "$changelog_file" ]]; then
        # Remove old header and add content after the new changes
        tail -n +12 "$changelog_file" >> "$temp_file"
    fi
    
    # Write the new changelog
    if [[ "$DRY_RUN" == false ]]; then
        mv "$temp_file" "$changelog_file"
        log_success "Updated $changelog_file"
    else
        log_info "Would write to $changelog_file:"
        cat "$temp_file"
        rm "$temp_file"
    fi
}

# =============================================================================
# Packaging Functions
# =============================================================================

create_package() {
    local version="$1"
    local package_dir="${PROJECT_ROOT}/release"
    local package_name="${PACKAGE_NAME}-${version}"
    
    log_info "Creating release package..."
    
    if [[ "$DRY_RUN" == true ]]; then
        log_info "Would create package: ${package_name}.tar.gz"
        return
    fi
    
    # Create release directory
    mkdir -p "$package_dir"
    
    # Create temporary directory for packaging
    local temp_dir=$(mktemp -d)
    local build_dir="${temp_dir}/${package_name}"
    mkdir -p "$build_dir"
    
    # Copy files to package
    log_info "Copying files to package..."
    
    # Copy source files
    cp -r "${PROJECT_ROOT}/src" "$build_dir/" 2>/dev/null || true
    cp -r "${PROJECT_ROOT}/FormalScience" "$build_dir/" 2>/dev/null || true
    cp -r "${PROJECT_ROOT}/Concept" "$build_dir/" 2>/dev/null || true
    cp -r "${PROJECT_ROOT}/Composed" "$build_dir/" 2>/dev/null || true
    cp -r "${PROJECT_ROOT}/docs" "$build_dir/" 2>/dev/null || true
    
    # Copy config files
    cp "${PROJECT_ROOT}/README.md" "$build_dir/" 2>/dev/null || true
    cp "${PROJECT_ROOT}/LICENSE" "$build_dir/" 2>/dev/null || true
    cp "${PROJECT_ROOT}/CHANGELOG.md" "$build_dir/" 2>/dev/null || true
    cp "${PROJECT_ROOT}/Cargo.toml" "$build_dir/" 2>/dev/null || true
    cp "${PROJECT_ROOT}/Cargo.lock" "$build_dir/" 2>/dev/null || true
    cp "${PROJECT_ROOT}/lakefile.toml" "$build_dir/" 2>/dev/null || true
    cp "${PROJECT_ROOT}/lake-manifest.json" "$build_dir/" 2>/dev/null || true
    cp "${PROJECT_ROOT}/lean-toolchain" "$build_dir/" 2>/dev/null || true
    
    # Create tarball
    local tarball="${package_dir}/${package_name}.tar.gz"
    tar czf "$tarball" -C "$temp_dir" "$package_name"
    
    # Create zip for Windows
    local zipfile="${package_dir}/${package_name}.zip"
    (cd "$temp_dir" && zip -r "$zipfile" "$package_name")
    
    # Cleanup
    rm -rf "$temp_dir"
    
    log_success "Created packages:"
    log_success "  - $tarball"
    log_success "  - $zipfile"
    
    # Calculate checksums
    log_info "Calculating checksums..."
    (cd "$package_dir" && sha256sum "${package_name}.tar.gz" > "${package_name}.tar.gz.sha256")
    (cd "$package_dir" && sha256sum "${package_name}.zip" > "${package_name}.zip.sha256")
}

# =============================================================================
# Git Functions
# =============================================================================

create_git_tag() {
    local version="$1"
    local tag="v${version}"
    
    log_info "Creating git tag: $tag"
    
    if [[ "$DRY_RUN" == true ]]; then
        log_info "Would run: git tag -a $tag -m \"Release $version\""
        return
    fi
    
    # Create annotated tag
    git tag -a "$tag" -m "Release $version"
    
    log_success "Created tag: $tag"
    log_info "To push the tag, run: git push origin $tag"
}

# =============================================================================
# Main Function
# =============================================================================

main() {
    log_info "FormalScience Release Script"
    log_info "============================"
    
    # Check if we're in a git repository
    if ! git rev-parse --git-dir > /dev/null 2>&1; then
        log_error "Not a git repository"
        exit 1
    fi
    
    # Check for uncommitted changes
    if [[ -n $(git status --porcelain) ]]; then
        log_warning "You have uncommitted changes"
        if [[ "$SKIP_CONFIRM" == false && "$DRY_RUN" == false ]]; then
            read -p "Continue anyway? (y/N) " -n 1 -r
            echo
            if [[ ! $REPLY =~ ^[Yy]$ ]]; then
                exit 1
            fi
        fi
    fi
    
    # Get current version
    local current_version=$(get_current_version)
    log_info "Current version: $current_version"
    
    # Calculate new version
    local new_version
    if [[ -n "$SPECIFIED_VERSION" ]]; then
        new_version="$SPECIFIED_VERSION"
    else
        new_version=$(bump_version "$current_version" "$VERSION_BUMP")
    fi
    
    log_info "New version: $new_version"
    
    # Confirm if not dry run and not skipping confirmation
    if [[ "$DRY_RUN" == false && "$SKIP_CONFIRM" == false && "$CHANGELOG_ONLY" == false ]]; then
        read -p "Continue with release? (y/N) " -n 1 -r
        echo
        if [[ ! $REPLY =~ ^[Yy]$ ]]; then
            exit 1
        fi
    fi
    
    # Generate changelog
    generate_changelog "$new_version"
    
    if [[ "$CHANGELOG_ONLY" == true ]]; then
        log_success "Changelog generated successfully!"
        exit 0
    fi
    
    # Update version in files
    update_version_in_files "$new_version"
    
    # Create package
    create_package "$new_version"
    
    # Commit changes
    if [[ "$DRY_RUN" == false ]]; then
        log_info "Committing changes..."
        git add -A
        git commit -m "chore(release): prepare for v${new_version}

- Update version to ${new_version}
- Update CHANGELOG.md"
        log_success "Committed changes"
    fi
    
    # Create git tag
    create_git_tag "$new_version"
    
    # Summary
    echo ""
    log_success "Release v${new_version} prepared successfully!"
    echo ""
    log_info "Next steps:"
    echo "  1. Review the changes: git show HEAD"
    echo "  2. Push the commit: git push origin main"
    echo "  3. Push the tag: git push origin v${new_version}"
    echo "  4. Create a release on GitHub"
    echo ""
    log_info "Release packages are in: ${PROJECT_ROOT}/release/"
}

# Run main function
parse_args "$@"
main
