/**
 * Sidebar Management
 * Handles sidebar toggle, mobile behavior, and responsive layout
 */

class SidebarManager {
    constructor() {
        this.sidebar = document.getElementById('sidebar');
        this.overlay = document.getElementById('sidebar-overlay');
        this.toggleButton = document.querySelector('.sidebar-toggle');
        this.main = document.getElementById('main');
        
        this.isOpen = false;
        this.isMobile = false;
        
        this.init();
    }

    init() {
        this.checkMobile();
        this.setupEventListeners();
        this.setupResizeListener();
        this.setupKeyboardNavigation();
        this.highlightCurrentPage();
    }

    checkMobile() {
        this.isMobile = window.innerWidth <= 768;
        
        if (this.isMobile) {
            this.sidebar?.classList.remove('is-open');
            this.isOpen = false;
        } else {
            this.sidebar?.classList.add('is-open');
            this.isOpen = true;
        }
        
        this.updateToggleButton();
    }

    setupEventListeners() {
        // Toggle button
        this.toggleButton?.addEventListener('click', () => {
            this.toggle();
        });

        // Overlay click (mobile)
        this.overlay?.addEventListener('click', () => {
            if (this.isMobile) {
                this.close();
            }
        });

        // Escape key
        document.addEventListener('keydown', (e) => {
            if (e.key === 'Escape' && this.isMobile && this.isOpen) {
                this.close();
            }
        });

        // Click outside sidebar on mobile
        document.addEventListener('click', (e) => {
            if (this.isMobile && this.isOpen) {
                const isClickInsideSidebar = this.sidebar?.contains(e.target);
                const isToggleButton = this.toggleButton?.contains(e.target);
                
                if (!isClickInsideSidebar && !isToggleButton) {
                    this.close();
                }
            }
        });

        // Navigation links
        const navLinks = document.querySelectorAll('.nav-link, .nav-sublink');
        navLinks.forEach(link => {
            link.addEventListener('click', () => {
                if (this.isMobile) {
                    this.close();
                }
            });
        });
    }

    setupResizeListener() {
        let resizeTimeout;
        window.addEventListener('resize', () => {
            clearTimeout(resizeTimeout);
            resizeTimeout = setTimeout(() => {
                this.checkMobile();
            }, 150);
        });
    }

    setupKeyboardNavigation() {
        // Focus management for accessibility
        const focusableElements = this.sidebar?.querySelectorAll(
            'a[href], button:not([disabled]), [tabindex]:not([tabindex="-1"])'
        );

        if (focusableElements) {
            const firstElement = focusableElements[0];
            const lastElement = focusableElements[focusableElements.length - 1];

            this.sidebar?.addEventListener('keydown', (e) => {
                if (e.key === 'Tab') {
                    if (e.shiftKey) {
                        if (document.activeElement === firstElement) {
                            e.preventDefault();
                            lastElement.focus();
                        }
                    } else {
                        if (document.activeElement === lastElement) {
                            e.preventDefault();
                            firstElement.focus();
                        }
                    }
                }
            });
        }
    }

    highlightCurrentPage() {
        const currentPath = window.location.pathname;
        const navLinks = document.querySelectorAll('.nav-link, .nav-sublink');
        
        navLinks.forEach(link => {
            const linkPath = new URL(link.href).pathname;
            
            if (linkPath === currentPath || 
                (currentPath.includes(linkPath) && linkPath !== '/')) {
                link.classList.add('active');
                link.setAttribute('aria-current', 'page');
                
                // Expand parent section if it's a subsection
                const parentSection = link.closest('.nav-subsections');
                if (parentSection) {
                    parentSection.style.display = 'block';
                }
            } else {
                link.classList.remove('active');
                link.removeAttribute('aria-current');
            }
        });
    }

    toggle() {
        if (this.isOpen) {
            this.close();
        } else {
            this.open();
        }
    }

    open() {
        this.isOpen = true;
        this.sidebar?.classList.add('is-open');
        this.overlay?.classList.add('is-visible');
        
        if (this.isMobile) {
            document.body.style.overflow = 'hidden';
        }
        
        this.updateToggleButton();
        
        // Focus first navigation item for accessibility
        const firstNavLink = this.sidebar?.querySelector('.nav-link');
        if (firstNavLink && this.isMobile) {
            setTimeout(() => firstNavLink.focus(), 100);
        }
    }

    close() {
        this.isOpen = false;
        this.sidebar?.classList.remove('is-open');
        this.overlay?.classList.remove('is-visible');
        
        if (this.isMobile) {
            document.body.style.overflow = '';
        }
        
        this.updateToggleButton();
    }

    updateToggleButton() {
        if (this.toggleButton) {
            this.toggleButton.setAttribute('aria-expanded', this.isOpen.toString());
            
            // Update icon
            const icon = this.toggleButton.querySelector('svg');
            if (icon && this.isOpen && this.isMobile) {
                // Change to X icon
                icon.innerHTML = `
                    <line x1="18" y1="6" x2="6" y2="18"></line>
                    <line x1="6" y1="6" x2="18" y2="18"></line>
                `;
            } else if (icon) {
                // Change to hamburger icon
                icon.innerHTML = `
                    <line x1="3" y1="6" x2="21" y2="6"></line>
                    <line x1="3" y1="12" x2="21" y2="12"></line>
                    <line x1="3" y1="18" x2="21" y2="18"></line>
                `;
            }
        }
    }

    // Public API
    getSidebarState() {
        return {
            isOpen: this.isOpen,
            isMobile: this.isMobile
        };
    }
}

// Add overlay styles
const overlayStyles = `
    .sidebar-overlay {
        position: fixed;
        top: 0;
        left: 0;
        right: 0;
        bottom: 0;
        background-color: rgba(0, 0, 0, 0.5);
        z-index: 850;
        opacity: 0;
        visibility: hidden;
        transition: opacity 0.25s ease-out, visibility 0.25s ease-out;
    }
    
    .sidebar-overlay.is-visible {
        opacity: 1;
        visibility: visible;
    }
    
    @media (min-width: 769px) {
        .sidebar-overlay {
            display: none;
        }
    }
`;

// Inject overlay styles
const styleSheet = document.createElement('style');
styleSheet.textContent = overlayStyles;
document.head.appendChild(styleSheet);

// Initialize sidebar manager when DOM is ready
if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', () => {
        window.sidebarManager = new SidebarManager();
    });
} else {
    window.sidebarManager = new SidebarManager();
}