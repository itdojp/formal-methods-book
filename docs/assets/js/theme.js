/**
 * Theme management for light/dark mode
 */

(function() {
    'use strict';
    
    // Constants
    const THEME_KEY = 'book-theme';
    const LEGACY_KEYS = ['theme']; // migrate previous key if present
    const THEME_LIGHT = 'light';
    const THEME_DARK = 'dark';

    function safeGetItem(key) {
        try {
            return localStorage.getItem(key);
        } catch (_) {
            return null;
        }
    }

    function safeSetItem(key, value) {
        try {
            localStorage.setItem(key, value);
        } catch (_) {}
    }

    function safeRemoveItem(key) {
        try {
            localStorage.removeItem(key);
        } catch (_) {}
    }

    function normalizeTheme(value) {
        if (value === THEME_DARK) return THEME_DARK;
        if (value === THEME_LIGHT) return THEME_LIGHT;
        return null;
    }

    function migrateLegacyTheme() {
        if (normalizeTheme(safeGetItem(THEME_KEY))) return;
        for (const key of LEGACY_KEYS) {
            const legacy = normalizeTheme(safeGetItem(key));
            if (legacy) {
                safeSetItem(THEME_KEY, legacy);
                safeRemoveItem(key);
                break;
            }
        }
    }
    
    // Get system preference
    function getSystemTheme() {
        if (typeof window.matchMedia !== 'function') {
            return THEME_LIGHT;
        }
        return window.matchMedia('(prefers-color-scheme: dark)').matches ? THEME_DARK : THEME_LIGHT;
    }
    
    // Get saved theme or system preference
    function getSavedTheme() {
        return normalizeTheme(safeGetItem(THEME_KEY)) || getSystemTheme();
    }
    
    // Apply theme to document
    function applyTheme(theme, persist = true) {
        document.documentElement.setAttribute('data-theme', theme);
        if (persist) {
            safeSetItem(THEME_KEY, theme);
        }
    }
    
    // Toggle theme
    function toggleTheme() {
        const currentTheme = document.documentElement.getAttribute('data-theme');
        const newTheme = currentTheme === THEME_LIGHT ? THEME_DARK : THEME_LIGHT;
        applyTheme(newTheme, true);
    }
    
    // Initialize theme
    function initTheme() {
        migrateLegacyTheme();

        // Only persist when user has explicitly selected a theme (stored value exists)
        const hadPreference = normalizeTheme(safeGetItem(THEME_KEY)) != null;
        const savedTheme = getSavedTheme();
        applyTheme(savedTheme, hadPreference);
        
        // Add event listener to theme toggle button
        const themeToggle = document.querySelector('.theme-toggle');
        if (themeToggle) {
            themeToggle.addEventListener('click', toggleTheme);
        }
        
        // Listen for system theme changes
        if (typeof window.matchMedia === 'function') {
            const mq = window.matchMedia('(prefers-color-scheme: dark)');
            const handler = (e) => {
                // Only apply system theme if user hasn't set a preference
                if (!normalizeTheme(safeGetItem(THEME_KEY))) {
                    applyTheme(e.matches ? THEME_DARK : THEME_LIGHT, false);
                }
            };
            if (mq.addEventListener) {
                mq.addEventListener('change', handler);
            } else if (mq.addListener) {
                mq.addListener(handler);
            }
        }
    }
    
    // Initialize when DOM is ready
    if (document.readyState === 'loading') {
        document.addEventListener('DOMContentLoaded', initTheme);
    } else {
        initTheme();
    }
})();
