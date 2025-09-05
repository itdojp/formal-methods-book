/**
 * Theme management for light/dark mode
 */

(function() {
    'use strict';
    
    // Constants
    const THEME_KEY = 'book-theme';
    const THEME_LIGHT = 'light';
    const THEME_DARK = 'dark';
    
    // Get system preference
    function getSystemTheme() {
        return window.matchMedia('(prefers-color-scheme: dark)').matches ? THEME_DARK : THEME_LIGHT;
    }
    
    // Get saved theme or system preference
    function getSavedTheme() {
        return localStorage.getItem(THEME_KEY) || getSystemTheme();
    }
    
    // Apply theme to document
    function applyTheme(theme) {
        document.documentElement.setAttribute('data-theme', theme);
        localStorage.setItem(THEME_KEY, theme);
    }
    
    // Toggle theme
    function toggleTheme() {
        const currentTheme = document.documentElement.getAttribute('data-theme');
        const newTheme = currentTheme === THEME_LIGHT ? THEME_DARK : THEME_LIGHT;
        applyTheme(newTheme);
    }
    
    // Initialize theme
    function initTheme() {
        // Apply saved theme
        const savedTheme = getSavedTheme();
        applyTheme(savedTheme);
        
        // Add event listener to theme toggle button
        const themeToggle = document.querySelector('.theme-toggle');
        if (themeToggle) {
            themeToggle.addEventListener('click', toggleTheme);
        }
        
        // Listen for system theme changes
        window.matchMedia('(prefers-color-scheme: dark)').addEventListener('change', (e) => {
            // Only apply system theme if user hasn't set a preference
            if (!localStorage.getItem(THEME_KEY)) {
                applyTheme(e.matches ? THEME_DARK : THEME_LIGHT);
            }
        });
    }
    
    // Initialize when DOM is ready
    if (document.readyState === 'loading') {
        document.addEventListener('DOMContentLoaded', initTheme);
    } else {
        initTheme();
    }
})();