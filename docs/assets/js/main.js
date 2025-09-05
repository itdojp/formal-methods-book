/**
 * Main JavaScript file - Additional utilities and enhancements
 */

(function() {
    'use strict';
    
    // Smooth scrolling for anchor links
    function initSmoothScrolling() {
        document.addEventListener('click', (e) => {
            const link = e.target.closest('a[href^="#"]');
            if (!link) return;
            
            e.preventDefault();
            const targetId = link.getAttribute('href').slice(1);
            const target = document.getElementById(targetId);
            
            if (target) {
                const headerHeight = document.querySelector('.book-header')?.offsetHeight || 0;
                const targetPosition = target.getBoundingClientRect().top + window.pageYOffset - headerHeight - 20;
                
                window.scrollTo({
                    top: targetPosition,
                    behavior: 'smooth'
                });
                
                // Update URL without jumping
                history.pushState(null, '', link.getAttribute('href'));
            }
        });
    }
    
    // Add IDs to headings for anchor links
    function addHeadingIds() {
        const headings = document.querySelectorAll('.page-content h1, .page-content h2, .page-content h3, .page-content h4, .page-content h5, .page-content h6');
        
        headings.forEach(heading => {
            if (!heading.id) {
                // Generate ID from heading text
                const text = heading.textContent.trim();
                const id = text
                    .toLowerCase()
                    .replace(/[^a-z0-9\u3040-\u309f\u30a0-\u30ff\u4e00-\u9faf\u3400-\u4dbf]+/g, '-')
                    .replace(/^-+|-+$/g, '');
                
                // Ensure unique ID
                let uniqueId = id;
                let counter = 1;
                while (document.getElementById(uniqueId)) {
                    uniqueId = `${id}-${counter}`;
                    counter++;
                }
                
                heading.id = uniqueId;
            }
            
            // Add anchor link
            if (!heading.querySelector('.heading-anchor')) {
                const anchor = document.createElement('a');
                anchor.className = 'heading-anchor';
                anchor.href = `#${heading.id}`;
                anchor.innerHTML = '#';
                anchor.setAttribute('aria-label', 'Anchor link');
                heading.appendChild(anchor);
            }
        });
    }
    
    // Table of Contents generator for current page
    function generateTOC() {
        const tocContainer = document.querySelector('.page-toc');
        if (!tocContainer) return;
        
        const headings = document.querySelectorAll('.page-content h2, .page-content h3');
        if (headings.length === 0) return;
        
        const toc = document.createElement('ul');
        toc.className = 'page-toc-list';
        
        let currentLevel = 2;
        let currentList = toc;
        const stack = [toc];
        
        headings.forEach(heading => {
            const level = parseInt(heading.tagName.charAt(1));
            const item = document.createElement('li');
            const link = document.createElement('a');
            
            link.href = `#${heading.id}`;
            link.textContent = heading.textContent.replace('#', '').trim();
            link.className = 'page-toc-link';
            
            if (level > currentLevel) {
                const sublist = document.createElement('ul');
                sublist.className = 'page-toc-sublist';
                currentList.lastElementChild?.appendChild(sublist);
                stack.push(sublist);
                currentList = sublist;
            } else if (level < currentLevel) {
                stack.pop();
                currentList = stack[stack.length - 1];
            }
            
            currentLevel = level;
            item.appendChild(link);
            currentList.appendChild(item);
        });
        
        tocContainer.appendChild(toc);
        
        // Highlight current section on scroll
        let scrollTimeout;
        window.addEventListener('scroll', () => {
            clearTimeout(scrollTimeout);
            scrollTimeout = setTimeout(updateTOCHighlight, 100);
        });
        
        updateTOCHighlight();
    }
    
    // Update TOC highlight based on scroll position
    function updateTOCHighlight() {
        const headings = document.querySelectorAll('.page-content h2, .page-content h3');
        const tocLinks = document.querySelectorAll('.page-toc-link');
        
        let currentHeading = null;
        const scrollPosition = window.scrollY + 100; // Offset for header
        
        headings.forEach(heading => {
            if (heading.offsetTop <= scrollPosition) {
                currentHeading = heading;
            }
        });
        
        tocLinks.forEach(link => {
            if (currentHeading && link.getAttribute('href') === `#${currentHeading.id}`) {
                link.classList.add('active');
            } else {
                link.classList.remove('active');
            }
        });
    }
    
    // External link handler
    function handleExternalLinks() {
        const links = document.querySelectorAll('a[href^="http"]');
        
        links.forEach(link => {
            if (link.hostname !== window.location.hostname) {
                link.setAttribute('target', '_blank');
                link.setAttribute('rel', 'noopener noreferrer');
                
                // Add external link icon
                if (!link.querySelector('.external-icon')) {
                    const icon = document.createElement('svg');
                    icon.className = 'external-icon';
                    icon.innerHTML = `
                        <svg width="12" height="12" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2">
                            <path d="M18 13v6a2 2 0 0 1-2 2H5a2 2 0 0 1-2-2V8a2 2 0 0 1 2-2h6"></path>
                            <polyline points="15 3 21 3 21 9"></polyline>
                            <line x1="10" y1="14" x2="21" y2="3"></line>
                        </svg>
                    `;
                    link.appendChild(icon);
                }
            }
        });
    }
    
    // Image loading enhancement
    function enhanceImages() {
        const images = document.querySelectorAll('.page-content img');
        
        images.forEach(img => {
            // Add loading attribute
            if (!img.hasAttribute('loading')) {
                img.setAttribute('loading', 'lazy');
            }
            
            // Add error handler
            img.addEventListener('error', function() {
                this.classList.add('error');
                this.alt = this.alt || 'Image failed to load';
            });
            
            // Make images clickable for full view
            if (!img.closest('a')) {
                img.style.cursor = 'zoom-in';
                img.addEventListener('click', () => {
                    openImageModal(img);
                });
            }
        });
    }
    
    // Open image in modal
    function openImageModal(img) {
        const modal = document.createElement('div');
        modal.className = 'image-modal';
        modal.innerHTML = `
            <div class="image-modal-content">
                <img src="${img.src}" alt="${img.alt}">
                <button class="image-modal-close">&times;</button>
            </div>
        `;
        
        document.body.appendChild(modal);
        
        // Close handlers
        const closeModal = () => {
            modal.remove();
        };
        
        modal.querySelector('.image-modal-close').addEventListener('click', closeModal);
        modal.addEventListener('click', (e) => {
            if (e.target === modal) closeModal();
        });
        
        document.addEventListener('keydown', function escHandler(e) {
            if (e.key === 'Escape') {
                closeModal();
                document.removeEventListener('keydown', escHandler);
            }
        });
    }
    
    // Add additional styles
    function addStyles() {
        const styles = `
            <style>
            /* Heading anchors */
            .heading-anchor {
                margin-left: 0.5rem;
                color: var(--text-muted);
                opacity: 0;
                transition: opacity 0.2s;
                text-decoration: none;
            }
            
            h1:hover .heading-anchor,
            h2:hover .heading-anchor,
            h3:hover .heading-anchor,
            h4:hover .heading-anchor,
            h5:hover .heading-anchor,
            h6:hover .heading-anchor {
                opacity: 1;
            }
            
            /* External link icon */
            .external-icon {
                display: inline-block;
                margin-left: 0.25rem;
                vertical-align: baseline;
            }
            
            /* Image modal */
            .image-modal {
                position: fixed;
                top: 0;
                left: 0;
                right: 0;
                bottom: 0;
                background: rgba(0, 0, 0, 0.9);
                display: flex;
                align-items: center;
                justify-content: center;
                z-index: 10000;
                padding: 2rem;
            }
            
            .image-modal-content {
                position: relative;
                max-width: 90vw;
                max-height: 90vh;
            }
            
            .image-modal-content img {
                max-width: 100%;
                max-height: 90vh;
                object-fit: contain;
            }
            
            .image-modal-close {
                position: absolute;
                top: -2rem;
                right: 0;
                background: transparent;
                border: none;
                color: white;
                font-size: 2rem;
                cursor: pointer;
                padding: 0.5rem;
            }
            
            /* Page TOC */
            .page-toc {
                position: sticky;
                top: calc(var(--header-height) + 2rem);
                float: right;
                width: 200px;
                margin-left: 2rem;
                padding: 1rem;
                background: var(--bg-secondary);
                border-radius: 6px;
                font-size: 0.875rem;
            }
            
            .page-toc-list {
                list-style: none;
                padding: 0;
                margin: 0;
            }
            
            .page-toc-sublist {
                list-style: none;
                padding-left: 1rem;
                margin: 0;
            }
            
            .page-toc-link {
                display: block;
                padding: 0.25rem 0;
                color: var(--text-secondary);
                text-decoration: none;
                transition: color 0.2s;
            }
            
            .page-toc-link:hover,
            .page-toc-link.active {
                color: var(--primary-color);
            }
            
            @media (max-width: 1280px) {
                .page-toc {
                    display: none;
                }
            }
            </style>
        `;
        
        document.head.insertAdjacentHTML('beforeend', styles);
    }
    
    // Initialize all features
    function init() {
        addStyles();
        initSmoothScrolling();
        addHeadingIds();
        generateTOC();
        handleExternalLinks();
        enhanceImages();
    }
    
    // Initialize when DOM is ready
    if (document.readyState === 'loading') {
        document.addEventListener('DOMContentLoaded', init);
    } else {
        init();
    }
})();