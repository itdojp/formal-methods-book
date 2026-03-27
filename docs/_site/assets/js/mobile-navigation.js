/**
 * Mobile Navigation JavaScript
 * Handles responsive navigation behavior and mobile-specific interactions
 */

(function() {
    'use strict';

    // Mobile navigation state
    let isMobileMenuOpen = false;
    let isInitialized = false;

    // DOM elements
    let mobileMenuToggle = null;
    let sidebar = null;
    let sidebarOverlay = null;
    let body = null;

    /**
     * Initialize mobile navigation
     */
    function initMobileNavigation() {
        if (isInitialized) return;

        // Get DOM elements
        mobileMenuToggle = document.querySelector('.mobile-menu-toggle');
        sidebar = document.querySelector('.book-sidebar');
        body = document.body;

        // Create overlay if it doesn't exist
        if (!document.querySelector('.book-sidebar-overlay')) {
            createSidebarOverlay();
        }
        sidebarOverlay = document.querySelector('.book-sidebar-overlay');

        // Set up event listeners
        setupEventListeners();

        // Handle initial state
        handleResize();

        isInitialized = true;
        console.log('[Mobile Nav] Initialized');
    }

    /**
     * Create sidebar overlay element
     */
    function createSidebarOverlay() {
        const overlay = document.createElement('div');
        overlay.className = 'book-sidebar-overlay';
        overlay.setAttribute('aria-hidden', 'true');
        document.body.appendChild(overlay);
    }

    /**
     * Set up all event listeners
     */
    function setupEventListeners() {
        // Mobile menu toggle
        if (mobileMenuToggle) {
            mobileMenuToggle.addEventListener('click', toggleMobileMenu);
            mobileMenuToggle.setAttribute('aria-expanded', 'false');
            mobileMenuToggle.setAttribute('aria-controls', 'mobile-sidebar');
        }

        // Overlay click to close
        if (sidebarOverlay) {
            sidebarOverlay.addEventListener('click', closeMobileMenu);
        }

        // Escape key to close
        document.addEventListener('keydown', handleKeydown);

        // Window resize
        window.addEventListener('resize', debounce(handleResize, 250));

        // Click outside sidebar to close (mobile only)
        document.addEventListener('click', handleOutsideClick);

        // Handle sidebar link clicks on mobile
        if (sidebar) {
            sidebar.addEventListener('click', handleSidebarLinkClick);
        }

        // Touch events for swipe gestures
        setupSwipeGestures();
    }

    /**
     * Toggle mobile menu open/closed
     */
    function toggleMobileMenu() {
        if (isMobileMenuOpen) {
            closeMobileMenu();
        } else {
            openMobileMenu();
        }
    }

    /**
     * Open mobile menu
     */
    function openMobileMenu() {
        if (!sidebar || !sidebarOverlay || !mobileMenuToggle) return;

        isMobileMenuOpen = true;
        
        // Add classes
        sidebar.classList.add('open');
        sidebarOverlay.classList.add('active');
        body.classList.add('mobile-menu-open');

        // Update ARIA attributes
        mobileMenuToggle.setAttribute('aria-expanded', 'true');
        sidebar.setAttribute('aria-hidden', 'false');
        sidebarOverlay.setAttribute('aria-hidden', 'false');

        // Focus management
        const firstFocusableElement = sidebar.querySelector('a, button, input, textarea, select');
        if (firstFocusableElement) {
            firstFocusableElement.focus();
        }

        // Prevent body scroll on mobile
        if (isMobile()) {
            body.style.overflow = 'hidden';
        }

        console.log('[Mobile Nav] Menu opened');
    }

    /**
     * Close mobile menu
     */
    function closeMobileMenu() {
        if (!sidebar || !sidebarOverlay || !mobileMenuToggle) return;

        isMobileMenuOpen = false;
        
        // Remove classes
        sidebar.classList.remove('open');
        sidebarOverlay.classList.remove('active');
        body.classList.remove('mobile-menu-open');

        // Update ARIA attributes
        mobileMenuToggle.setAttribute('aria-expanded', 'false');
        sidebar.setAttribute('aria-hidden', 'true');
        sidebarOverlay.setAttribute('aria-hidden', 'true');

        // Restore body scroll
        body.style.overflow = '';

        // Return focus to toggle button
        if (document.activeElement !== document.body) {
            mobileMenuToggle.focus();
        }

        console.log('[Mobile Nav] Menu closed');
    }

    /**
     * Handle keyboard events
     */
    function handleKeydown(event) {
        if (event.key === 'Escape' && isMobileMenuOpen) {
            closeMobileMenu();
        }
    }

    /**
     * Handle window resize
     */
    function handleResize() {
        const isCurrentlyMobile = isMobile();
        
        // Close mobile menu if window becomes desktop size
        if (!isCurrentlyMobile && isMobileMenuOpen) {
            closeMobileMenu();
        }

        // Update ARIA attributes based on screen size
        if (sidebar && mobileMenuToggle) {
            if (isCurrentlyMobile) {
                sidebar.setAttribute('aria-hidden', isMobileMenuOpen ? 'false' : 'true');
            } else {
                sidebar.setAttribute('aria-hidden', 'false');
            }
        }
    }

    /**
     * Handle clicks outside the sidebar
     */
    function handleOutsideClick(event) {
        if (!isMobileMenuOpen || !isMobile()) return;

        const isClickInsideSidebar = sidebar && sidebar.contains(event.target);
        const isClickOnToggle = mobileMenuToggle && mobileMenuToggle.contains(event.target);

        if (!isClickInsideSidebar && !isClickOnToggle) {
            closeMobileMenu();
        }
    }

    /**
     * Handle sidebar link clicks
     */
    function handleSidebarLinkClick(event) {
        // Close mobile menu when a link is clicked (on mobile)
        if (isMobile() && isMobileMenuOpen && event.target.tagName === 'A') {
            // Small delay to allow navigation to start
            setTimeout(closeMobileMenu, 100);
        }
    }

    /**
     * Set up swipe gestures for mobile
     */
    function setupSwipeGestures() {
        let startX = 0;
        let startY = 0;
        let isScrolling = false;

        document.addEventListener('touchstart', function(event) {
            if (!isMobile()) return;

            startX = event.touches[0].clientX;
            startY = event.touches[0].clientY;
            isScrolling = false;
        }, { passive: true });

        document.addEventListener('touchmove', function(event) {
            if (!isMobile() || !startX || !startY) return;

            const deltaX = event.touches[0].clientX - startX;
            const deltaY = event.touches[0].clientY - startY;

            // Determine if this is a vertical scroll
            if (Math.abs(deltaY) > Math.abs(deltaX)) {
                isScrolling = true;
            }
        }, { passive: true });

        document.addEventListener('touchend', function(event) {
            if (!isMobile() || !startX || !startY || isScrolling) return;

            const deltaX = event.changedTouches[0].clientX - startX;
            const swipeThreshold = 100;

            // Swipe right to open menu (from left edge)
            if (deltaX > swipeThreshold && startX < 50 && !isMobileMenuOpen) {
                openMobileMenu();
            }
            // Swipe left to close menu
            else if (deltaX < -swipeThreshold && isMobileMenuOpen) {
                closeMobileMenu();
            }

            // Reset
            startX = 0;
            startY = 0;
            isScrolling = false;
        }, { passive: true });
    }

    /**
     * Check if current viewport is mobile size
     */
    function isMobile() {
        return window.innerWidth < 768;
    }

    /**
     * Debounce function for performance
     */
    function debounce(func, wait) {
        let timeout;
        return function executedFunction(...args) {
            const later = () => {
                clearTimeout(timeout);
                func(...args);
            };
            clearTimeout(timeout);
            timeout = setTimeout(later, wait);
        };
    }

    /**
     * Handle smooth scrolling for anchor links
     */
    function initSmoothScrolling() {
        document.addEventListener('click', function(event) {
            const link = event.target.closest('a[href^="#"]');
            if (!link) return;

            const targetId = link.getAttribute('href').substring(1);
            const target = document.getElementById(targetId);
            
            if (target) {
                event.preventDefault();
                
                // Close mobile menu if open
                if (isMobileMenuOpen) {
                    closeMobileMenu();
                }

                // Scroll to target with offset for fixed header
                const headerHeight = 60; // Adjust based on your header height
                const targetPosition = target.offsetTop - headerHeight;
                
                window.scrollTo({
                    top: targetPosition,
                    behavior: 'smooth'
                });

                // Update URL hash
                if (history.pushState) {
                    history.pushState(null, null, '#' + targetId);
                }
            }
        });
    }

    /**
     * Initialize responsive tables
     */
    function initResponsiveTables() {
        const tables = document.querySelectorAll('table');
        
        tables.forEach(table => {
            if (!table.closest('.responsive-table')) {
                const wrapper = document.createElement('div');
                wrapper.className = 'responsive-table';
                table.parentNode.insertBefore(wrapper, table);
                wrapper.appendChild(table);
            }
        });
    }

    /**
     * Handle orientation change
     */
    function handleOrientationChange() {
        // Close mobile menu on orientation change
        if (isMobileMenuOpen) {
            closeMobileMenu();
        }

        // Trigger resize handling after orientation change
        setTimeout(handleResize, 100);
    }

    /**
     * Initialize touch improvements
     */
    function initTouchImprovements() {
        // Add touch class to body for CSS styling
        if ('ontouchstart' in window || navigator.maxTouchPoints > 0) {
            body.classList.add('touch-device');
        }

        // Improve touch targets
        const links = document.querySelectorAll('a');
        links.forEach(link => {
            if (link.offsetHeight < 44 || link.offsetWidth < 44) {
                link.classList.add('touch-target-small');
            }
        });
    }

    /**
     * Initialize viewport meta tag if missing
     */
    function ensureViewportMeta() {
        let viewportMeta = document.querySelector('meta[name="viewport"]');
        
        if (!viewportMeta) {
            viewportMeta = document.createElement('meta');
            viewportMeta.name = 'viewport';
            viewportMeta.content = 'width=device-width, initial-scale=1.0, shrink-to-fit=no';
            document.head.appendChild(viewportMeta);
            console.log('[Mobile Nav] Added viewport meta tag');
        }
    }

    /**
     * Main initialization function
     */
    function init() {
        // Wait for DOM to be ready
        if (document.readyState === 'loading') {
            document.addEventListener('DOMContentLoaded', init);
            return;
        }

        // Ensure viewport meta tag exists
        ensureViewportMeta();

        // Initialize all mobile features
        initMobileNavigation();
        initSmoothScrolling();
        initResponsiveTables();
        initTouchImprovements();

        // Handle orientation change
        window.addEventListener('orientationchange', handleOrientationChange);

        console.log('[Mobile Nav] All mobile features initialized');
    }

    /**
     * Public API
     */
    window.MobileNavigation = {
        init: init,
        openMenu: openMobileMenu,
        closeMenu: closeMobileMenu,
        toggleMenu: toggleMobileMenu,
        isMenuOpen: () => isMobileMenuOpen,
        isMobile: isMobile
    };

    // Auto-initialize
    init();

})();