/**
 * FormalScience Project Website - Main Application Script
 * Features: Theme toggle, search, navigation, dynamic loading
 */

(function() {
  'use strict';

  // ============================================
  // Configuration
  // ============================================
  const CONFIG = {
    themeKey: 'formalscience-theme',
    defaultTheme: 'light',
    searchDelay: 300,
    scrollOffset: 100
  };

  // ============================================
  // Search Data
  // ============================================
  const searchData = [
    { title: '首页', url: 'index.html', desc: '项目主页，包含介绍和快速开始', category: '页面' },
    { title: '关于我们', url: 'about.html', desc: '项目背景、目标和团队介绍', category: '页面' },
    { title: '模块导航', url: 'modules.html', desc: '8大模块的详细介绍', category: '页面' },
    { title: '资源中心', url: 'resources.html', desc: '代码示例、练习题和工具', category: '页面' },
    { title: '数学基础', url: '#', desc: '集合论、数理逻辑、图论', category: '模块' },
    { title: '形式语言', url: '#', desc: '自动机理论、形式文法', category: '模块' },
    { title: '类型理论', url: '#', desc: 'Lambda演算、类型系统', category: '模块' },
    { title: '证明助手', url: '#', desc: 'Coq、Isabelle、Lean', category: '模块' },
    { title: '程序验证', url: '#', desc: '霍尔逻辑、模型检测', category: '模块' },
    { title: '语义理论', url: '#', desc: '操作语义、指称语义', category: '模块' },
    { title: '代数规范', url: '#', desc: '抽象数据类型、代数结构', category: '模块' },
    { title: '形式化方法', url: '#', desc: '定理证明、SAT/SMT求解', category: '模块' },
    { title: '快速开始指南', url: '#', desc: '5分钟上手教程', category: '资源' },
    { title: 'API文档', url: '#', desc: '完整的API参考手册', category: '资源' },
    { title: '视频教程', url: '#', desc: '系列教学视频', category: '资源' },
    { title: '练习题库', url: '#', desc: '配套练习和答案', category: '资源' }
  ];

  // ============================================
  // Theme Manager
  // ============================================
  const ThemeManager = {
    init() {
      this.themeToggle = document.querySelector('.theme-toggle');
      this.html = document.documentElement;
      
      if (this.themeToggle) {
        this.themeToggle.addEventListener('click', () => this.toggle());
      }
      
      // Load saved theme or detect system preference
      const savedTheme = localStorage.getItem(CONFIG.themeKey);
      const prefersDark = window.matchMedia('(prefers-color-scheme: dark)').matches;
      const theme = savedTheme || (prefersDark ? 'dark' : CONFIG.defaultTheme);
      
      this.set(theme);
      
      // Listen for system theme changes
      window.matchMedia('(prefers-color-scheme: dark)').addEventListener('change', (e) => {
        if (!localStorage.getItem(CONFIG.themeKey)) {
          this.set(e.matches ? 'dark' : 'light');
        }
      });
    },

    set(theme) {
      this.html.setAttribute('data-theme', theme);
      localStorage.setItem(CONFIG.themeKey, theme);
      this.dispatchEvent(theme);
    },

    toggle() {
      const current = this.html.getAttribute('data-theme');
      const next = current === 'dark' ? 'light' : 'dark';
      this.set(next);
    },

    dispatchEvent(theme) {
      window.dispatchEvent(new CustomEvent('themechange', { detail: { theme } }));
    }
  };

  // ============================================
  // Search Manager
  // ============================================
  const SearchManager = {
    init() {
      this.searchInput = document.getElementById('searchInput');
      this.searchResults = document.querySelector('.search-results');
      this.searchTimeout = null;
      
      if (this.searchInput) {
        this.searchInput.addEventListener('input', (e) => this.handleInput(e));
        this.searchInput.addEventListener('focus', () => this.showResults());
        this.searchInput.addEventListener('keydown', (e) => this.handleKeydown(e));
      }
      
      // Close search when clicking outside
      document.addEventListener('click', (e) => {
        if (!e.target.closest('.search-box')) {
          this.hideResults();
        }
      });
    },

    handleInput(e) {
      clearTimeout(this.searchTimeout);
      const query = e.target.value.trim().toLowerCase();
      
      if (query.length === 0) {
        this.hideResults();
        return;
      }
      
      this.searchTimeout = setTimeout(() => {
        this.performSearch(query);
      }, CONFIG.searchDelay);
    },

    handleKeydown(e) {
      if (e.key === 'Escape') {
        this.hideResults();
        this.searchInput.blur();
      }
    },

    performSearch(query) {
      const results = searchData.filter(item => 
        item.title.toLowerCase().includes(query) ||
        item.desc.toLowerCase().includes(query) ||
        item.category.toLowerCase().includes(query)
      );
      
      this.renderResults(results, query);
    },

    renderResults(results, query) {
      if (!this.searchResults) return;
      
      if (results.length === 0) {
        this.searchResults.innerHTML = `
          <div class="search-result-item">
            <p>未找到与 "${query}" 相关的内容</p>
          </div>
        `;
      } else {
        this.searchResults.innerHTML = results.map(item => `
          <div class="search-result-item" onclick="window.location.href='${item.url}'">
            <h4>${this.highlightMatch(item.title, query)}</h4>
            <p>${item.category} · ${this.highlightMatch(item.desc, query)}</p>
          </div>
        `).join('');
      }
      
      this.showResults();
    },

    highlightMatch(text, query) {
      const regex = new RegExp(`(${query})`, 'gi');
      return text.replace(regex, '<mark style="background: var(--primary-color); color: white; padding: 0 2px; border-radius: 2px;">$1</mark>');
    },

    showResults() {
      if (this.searchResults) {
        this.searchResults.classList.add('active');
      }
    },

    hideResults() {
      if (this.searchResults) {
        this.searchResults.classList.remove('active');
      }
    }
  };

  // ============================================
  // Navigation Manager
  // ============================================
  const NavigationManager = {
    init() {
      this.menuToggle = document.querySelector('.menu-toggle');
      this.navLinks = document.querySelector('.nav-links');
      this.header = document.querySelector('.header');
      
      // Mobile menu toggle
      if (this.menuToggle && this.navLinks) {
        this.menuToggle.addEventListener('click', () => this.toggleMenu());
      }
      
      // Active nav highlighting
      this.highlightActiveNav();
      
      // Header scroll effect
      window.addEventListener('scroll', () => this.handleScroll());
      
      // Smooth scroll for anchor links
      document.querySelectorAll('a[href^="#"]').forEach(anchor => {
        anchor.addEventListener('click', (e) => this.handleAnchorClick(e));
      });
    },

    toggleMenu() {
      this.navLinks.classList.toggle('active');
      const isOpen = this.navLinks.classList.contains('active');
      this.menuToggle.setAttribute('aria-expanded', isOpen);
    },

    highlightActiveNav() {
      const currentPage = window.location.pathname.split('/').pop() || 'index.html';
      
      document.querySelectorAll('.nav-links a').forEach(link => {
        const linkPage = link.getAttribute('href');
        if (linkPage === currentPage || (currentPage === '' && linkPage === 'index.html')) {
          link.classList.add('active');
        }
      });
    },

    handleScroll() {
      if (this.header) {
        if (window.scrollY > 10) {
          this.header.classList.add('scrolled');
        } else {
          this.header.classList.remove('scrolled');
        }
      }
    },

    handleAnchorClick(e) {
      const href = e.currentTarget.getAttribute('href');
      if (href === '#') return;
      
      const target = document.querySelector(href);
      if (target) {
        e.preventDefault();
        const offset = target.offsetTop - CONFIG.scrollOffset;
        window.scrollTo({ top: offset, behavior: 'smooth' });
      }
    }
  };

  // ============================================
  // Scroll to Top Manager
  // ============================================
  const ScrollTopManager = {
    init() {
      this.button = document.querySelector('.scroll-top');
      
      if (this.button) {
        window.addEventListener('scroll', () => this.toggleVisibility());
        this.button.addEventListener('click', () => this.scrollToTop());
      }
    },

    toggleVisibility() {
      if (window.scrollY > 500) {
        this.button.classList.add('visible');
      } else {
        this.button.classList.remove('visible');
      }
    },

    scrollToTop() {
      window.scrollTo({ top: 0, behavior: 'smooth' });
    }
  };

  // ============================================
  // Animation Manager
  // ============================================
  const AnimationManager = {
    init() {
      this.animatedElements = document.querySelectorAll('[data-animate]');
      
      if (this.animatedElements.length > 0) {
        this.observer = new IntersectionObserver(
          (entries) => this.handleIntersection(entries),
          { threshold: 0.1, rootMargin: '0px 0px -50px 0px' }
        );
        
        this.animatedElements.forEach(el => {
          el.style.opacity = '0';
          el.style.transform = 'translateY(20px)';
          this.observer.observe(el);
        });
      }
    },

    handleIntersection(entries) {
      entries.forEach(entry => {
        if (entry.isIntersecting) {
          const el = entry.target;
          const delay = el.dataset.delay || 0;
          
          setTimeout(() => {
            el.style.transition = 'opacity 0.5s ease, transform 0.5s ease';
            el.style.opacity = '1';
            el.style.transform = 'translateY(0)';
          }, delay);
          
          this.observer.unobserve(el);
        }
      });
    }
  };

  // ============================================
  // Stats Counter Animation
  // ============================================
  const StatsManager = {
    init() {
      this.stats = document.querySelectorAll('.stat-number[data-count]');
      
      if (this.stats.length > 0) {
        this.observer = new IntersectionObserver(
          (entries) => this.handleIntersection(entries),
          { threshold: 0.5 }
        );
        
        this.stats.forEach(stat => this.observer.observe(stat));
      }
    },

    handleIntersection(entries) {
      entries.forEach(entry => {
        if (entry.isIntersecting) {
          this.animateCounter(entry.target);
          this.observer.unobserve(entry.target);
        }
      });
    },

    animateCounter(element) {
      const target = parseInt(element.dataset.count, 10);
      const duration = 2000;
      const step = target / (duration / 16);
      let current = 0;
      
      const updateCounter = () => {
        current += step;
        if (current < target) {
          element.textContent = Math.floor(current).toLocaleString();
          requestAnimationFrame(updateCounter);
        } else {
          element.textContent = target.toLocaleString();
        }
      };
      
      updateCounter();
    }
  };

  // ============================================
  // Module Cards Interaction
  // ============================================
  const ModuleManager = {
    init() {
      this.cards = document.querySelectorAll('.module-card');
      
      this.cards.forEach(card => {
        card.addEventListener('click', () => this.handleCardClick(card));
        card.addEventListener('mouseenter', () => this.handleCardHover(card, true));
        card.addEventListener('mouseleave', () => this.handleCardHover(card, false));
      });
    },

    handleCardClick(card) {
      const link = card.querySelector('.module-link');
      if (link) {
        window.location.href = link.getAttribute('href');
      }
    },

    handleCardHover(card, isHovering) {
      if (isHovering) {
        card.style.transform = 'translateY(-4px)';
      } else {
        card.style.transform = '';
      }
    }
  };

  // ============================================
  // Resource Cards Interaction
  // ============================================
  const ResourceManager = {
    init() {
      this.cards = document.querySelectorAll('.resource-card');
      
      this.cards.forEach(card => {
        card.addEventListener('click', (e) => this.handleCardClick(e, card));
      });
    },

    handleCardClick(e, card) {
      // Don't navigate if clicking on a link inside the card
      if (e.target.closest('a')) return;
      
      const firstLink = card.querySelector('a');
      if (firstLink) {
        window.location.href = firstLink.getAttribute('href');
      }
    }
  };

  // ============================================
  // Keyboard Navigation
  // ============================================
  const KeyboardManager = {
    init() {
      document.addEventListener('keydown', (e) => this.handleKeydown(e));
    },

    handleKeydown(e) {
      // Ctrl/Cmd + K for search
      if ((e.ctrlKey || e.metaKey) && e.key === 'k') {
        e.preventDefault();
        const searchInput = document.getElementById('searchInput');
        if (searchInput) {
          searchInput.focus();
        }
      }
      
      // Escape to close mobile menu
      if (e.key === 'Escape') {
        const navLinks = document.querySelector('.nav-links');
        if (navLinks && navLinks.classList.contains('active')) {
          navLinks.classList.remove('active');
        }
      }
    }
  };

  // ============================================
  // Notification System
  // ============================================
  const NotificationManager = {
    show(message, type = 'info', duration = 3000) {
      const notification = document.createElement('div');
      notification.className = `notification notification-${type}`;
      notification.innerHTML = `
        <span class="notification-message">${message}</span>
        <button class="notification-close" aria-label="关闭">&times;</button>
      `;
      
      // Add styles
      notification.style.cssText = `
        position: fixed;
        top: calc(var(--header-height) + 1rem);
        right: 1rem;
        background: var(--bg-card);
        border: 1px solid var(--border-color);
        border-radius: var(--radius-lg);
        padding: 1rem 1.5rem;
        box-shadow: var(--shadow-xl);
        z-index: 9999;
        display: flex;
        align-items: center;
        gap: 1rem;
        min-width: 300px;
        animation: slideIn 0.3s ease;
      `;
      
      // Add animation keyframes if not exists
      if (!document.getElementById('notification-styles')) {
        const style = document.createElement('style');
        style.id = 'notification-styles';
        style.textContent = `
          @keyframes slideIn {
            from { transform: translateX(100%); opacity: 0; }
            to { transform: translateX(0); opacity: 1; }
          }
          @keyframes slideOut {
            from { transform: translateX(0); opacity: 1; }
            to { transform: translateX(100%); opacity: 0; }
          }
          .notification-close {
            background: none;
            border: none;
            color: var(--text-muted);
            font-size: 1.25rem;
            cursor: pointer;
            padding: 0;
            width: 1.5rem;
            height: 1.5rem;
            display: flex;
            align-items: center;
            justify-content: center;
            border-radius: var(--radius-md);
          }
          .notification-close:hover {
            background: var(--bg-tertiary);
            color: var(--text-primary);
          }
        `;
        document.head.appendChild(style);
      }
      
      document.body.appendChild(notification);
      
      // Close button
      notification.querySelector('.notification-close').addEventListener('click', () => {
        this.close(notification);
      });
      
      // Auto close
      if (duration > 0) {
        setTimeout(() => this.close(notification), duration);
      }
    },

    close(notification) {
      notification.style.animation = 'slideOut 0.3s ease forwards';
      setTimeout(() => notification.remove(), 300);
    }
  };

  // ============================================
  // Initialize Application
  // ============================================
  function init() {
    // Initialize all managers
    ThemeManager.init();
    SearchManager.init();
    NavigationManager.init();
    ScrollTopManager.init();
    AnimationManager.init();
    StatsManager.init();
    ModuleManager.init();
    ResourceManager.init();
    KeyboardManager.init();
    
    // Log initialization
    console.log('🚀 FormalScience Website initialized successfully!');
    console.log('   - Theme: ' + document.documentElement.getAttribute('data-theme'));
    console.log('   - Press Ctrl+K to search');
  }

  // Run initialization when DOM is ready
  if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', init);
  } else {
    init();
  }

  // Expose API to global scope for debugging
  window.FormalScience = {
    theme: ThemeManager,
    search: SearchManager,
    notify: (msg, type) => NotificationManager.show(msg, type),
    version: '1.0.0'
  };

})();
