/**
 * Code Copy Functionality
 * Adds copy buttons to code blocks with enhanced UX
 */

class CodeCopyManager {
    constructor() {
        this.init();
    }

    init() {
        this.addCopyButtons();
        this.setupEventListeners();
    }

    addCopyButtons() {
        const codeBlocks = document.querySelectorAll('pre code');
        
        codeBlocks.forEach((codeBlock, index) => {
            const pre = codeBlock.parentElement;
            
            // Skip if button already exists
            if (pre.querySelector('.code-copy-button')) {
                return;
            }

            // Create wrapper if it doesn't exist
            if (!pre.classList.contains('code-block-wrapper')) {
                const wrapper = document.createElement('div');
                wrapper.className = 'code-block-wrapper';
                pre.parentNode.insertBefore(wrapper, pre);
                wrapper.appendChild(pre);
            }

            // Create copy button
            const copyButton = this.createCopyButton(index);
            
            // Add button to the pre element
            pre.style.position = 'relative';
            pre.appendChild(copyButton);
            
            // Add language label if available
            this.addLanguageLabel(pre, codeBlock);
        });
    }

    createCopyButton(index) {
        const button = document.createElement('button');
        button.className = 'code-copy-button';
        button.setAttribute('aria-label', 'Copy code to clipboard');
        button.setAttribute('data-code-index', index);
        
        button.innerHTML = `
            <svg class="copy-icon" width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2">
                <rect x="9" y="9" width="13" height="13" rx="2" ry="2"></rect>
                <path d="M5 15H4a2 2 0 01-2-2V4a2 2 0 012-2h9a2 2 0 012 2v1"></path>
            </svg>
            <svg class="check-icon" width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" style="display: none;">
                <polyline points="20,6 9,17 4,12"></polyline>
            </svg>
            <span class="copy-text">Copy</span>
        `;
        
        return button;
    }

    addLanguageLabel(pre, codeBlock) {
        // Try to detect language from class names
        const classes = codeBlock.className || '';
        const languageMatch = classes.match(/language-(\w+)/);
        
        if (languageMatch) {
            const language = languageMatch[1];
            const label = document.createElement('div');
            label.className = 'code-language-label';
            label.textContent = this.getLanguageDisplayName(language);
            pre.appendChild(label);
        }
    }

    getLanguageDisplayName(lang) {
        const languageMap = {
            'js': 'JavaScript',
            'javascript': 'JavaScript',
            'ts': 'TypeScript',
            'typescript': 'TypeScript',
            'py': 'Python',
            'python': 'Python',
            'rb': 'Ruby',
            'ruby': 'Ruby',
            'php': 'PHP',
            'java': 'Java',
            'c': 'C',
            'cpp': 'C++',
            'cs': 'C#',
            'go': 'Go',
            'rs': 'Rust',
            'rust': 'Rust',
            'sh': 'Shell',
            'bash': 'Bash',
            'zsh': 'Zsh',
            'powershell': 'PowerShell',
            'sql': 'SQL',
            'html': 'HTML',
            'css': 'CSS',
            'scss': 'SCSS',
            'sass': 'Sass',
            'less': 'Less',
            'json': 'JSON',
            'xml': 'XML',
            'yaml': 'YAML',
            'yml': 'YAML',
            'toml': 'TOML',
            'ini': 'INI',
            'dockerfile': 'Dockerfile',
            'docker': 'Docker',
            'nginx': 'Nginx',
            'apache': 'Apache',
            'md': 'Markdown',
            'markdown': 'Markdown'
        };
        
        return languageMap[lang.toLowerCase()] || lang.toUpperCase();
    }

    setupEventListeners() {
        document.addEventListener('click', (e) => {
            if (e.target.closest('.code-copy-button')) {
                e.preventDefault();
                this.handleCopyClick(e.target.closest('.code-copy-button'));
            }
        });
    }

    async handleCopyClick(button) {
        const pre = button.closest('pre');
        const codeBlock = pre.querySelector('code');
        
        if (!codeBlock) return;

        try {
            // Get the text content, preserving line breaks
            const code = this.getCleanCodeText(codeBlock);
            
            // Copy to clipboard
            await this.copyToClipboard(code);
            
            // Show success feedback
            this.showCopySuccess(button);
            
            // Track analytics if available
            if (typeof gtag !== 'undefined') {
                gtag('event', 'code_copy', {
                    'event_category': 'engagement',
                    'event_label': 'code_block'
                });
            }
            
        } catch (error) {
            console.error('Failed to copy code:', error);
            this.showCopyError(button);
        }
    }

    getCleanCodeText(codeElement) {
        // Clone the element to avoid modifying the original
        const clone = codeElement.cloneNode(true);
        
        // Remove line numbers if they exist
        const lineNumbers = clone.querySelectorAll('.line-number, .lineno');
        lineNumbers.forEach(el => el.remove());
        
        // Remove syntax highlighting spans but keep their text content
        const spans = clone.querySelectorAll('span[class*="highlight"], span[class*="token"]');
        spans.forEach(span => {
            const text = document.createTextNode(span.textContent);
            span.parentNode.replaceChild(text, span);
        });
        
        // Get text content and clean it up
        let text = clone.textContent || clone.innerText;
        
        // Remove leading/trailing whitespace
        text = text.trim();
        
        // Normalize line endings
        text = text.replace(/\r\n/g, '\n').replace(/\r/g, '\n');
        
        return text;
    }

    async copyToClipboard(text) {
        if (navigator.clipboard && window.isSecureContext) {
            // Use modern clipboard API
            await navigator.clipboard.writeText(text);
        } else {
            // Fallback for older browsers
            return this.fallbackCopyToClipboard(text);
        }
    }

    fallbackCopyToClipboard(text) {
        return new Promise((resolve, reject) => {
            const textArea = document.createElement('textarea');
            textArea.value = text;
            textArea.style.position = 'fixed';
            textArea.style.left = '-999999px';
            textArea.style.top = '-999999px';
            document.body.appendChild(textArea);
            textArea.focus();
            textArea.select();
            
            try {
                const successful = document.execCommand('copy');
                document.body.removeChild(textArea);
                
                if (successful) {
                    resolve();
                } else {
                    reject(new Error('Copy command failed'));
                }
            } catch (error) {
                document.body.removeChild(textArea);
                reject(error);
            }
        });
    }

    showCopySuccess(button) {
        const copyIcon = button.querySelector('.copy-icon');
        const checkIcon = button.querySelector('.check-icon');
        const copyText = button.querySelector('.copy-text');
        
        // Update visual state
        copyIcon.style.display = 'none';
        checkIcon.style.display = 'block';
        copyText.textContent = 'Copied!';
        button.classList.add('copy-success');
        
        // Reset after 2 seconds
        setTimeout(() => {
            copyIcon.style.display = 'block';
            checkIcon.style.display = 'none';
            copyText.textContent = 'Copy';
            button.classList.remove('copy-success');
        }, 2000);
    }

    showCopyError(button) {
        const copyText = button.querySelector('.copy-text');
        const originalText = copyText.textContent;
        
        copyText.textContent = 'Failed';
        button.classList.add('copy-error');
        
        setTimeout(() => {
            copyText.textContent = originalText;
            button.classList.remove('copy-error');
        }, 2000);
    }
}

// Add styles for code copy functionality
const copyStyles = `
    .code-block-wrapper {
        position: relative;
        margin: var(--space-4) 0;
    }
    
    .code-copy-button {
        position: absolute;
        top: var(--space-2);
        right: var(--space-2);
        background: var(--color-bg-secondary);
        border: 1px solid var(--color-border);
        border-radius: var(--radius-sm);
        padding: var(--space-2);
        cursor: pointer;
        display: flex;
        align-items: center;
        gap: var(--space-1);
        font-size: var(--font-size-xs);
        color: var(--color-text-secondary);
        transition: all var(--transition-fast);
        z-index: 10;
        opacity: 0;
        transform: translateY(-2px);
    }
    
    pre:hover .code-copy-button {
        opacity: 1;
        transform: translateY(0);
    }
    
    .code-copy-button:hover {
        background: var(--color-primary);
        color: white;
        border-color: var(--color-primary);
    }
    
    .code-copy-button:focus {
        outline: 2px solid var(--color-primary);
        outline-offset: 2px;
        opacity: 1;
    }
    
    .code-copy-button.copy-success {
        background: var(--color-success);
        color: white;
        border-color: var(--color-success);
    }
    
    .code-copy-button.copy-error {
        background: var(--color-danger);
        color: white;
        border-color: var(--color-danger);
    }
    
    .code-language-label {
        position: absolute;
        top: var(--space-2);
        left: var(--space-2);
        background: var(--color-text-muted);
        color: white;
        padding: var(--space-1) var(--space-2);
        border-radius: var(--radius-sm);
        font-size: var(--font-size-xs);
        font-weight: 500;
        text-transform: uppercase;
        letter-spacing: 0.05em;
        z-index: 10;
    }
    
    /* Mobile adjustments */
    @media (max-width: 768px) {
        .code-copy-button {
            opacity: 1;
            transform: translateY(0);
            position: relative;
            top: auto;
            right: auto;
            margin-bottom: var(--space-2);
            align-self: flex-end;
        }
        
        pre {
            display: flex;
            flex-direction: column;
        }
        
        pre code {
            order: 2;
        }
        
        .code-language-label {
            position: relative;
            top: auto;
            left: auto;
            align-self: flex-start;
            order: 1;
            margin-bottom: var(--space-2);
        }
    }
    
    /* High contrast mode */
    @media (prefers-contrast: high) {
        .code-copy-button {
            border-width: 2px;
        }
    }
    
    /* Reduced motion */
    @media (prefers-reduced-motion: reduce) {
        .code-copy-button {
            transition: none;
        }
    }
`;

// Inject styles
const styleSheet = document.createElement('style');
styleSheet.textContent = copyStyles;
document.head.appendChild(styleSheet);

// Initialize when DOM is ready
if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', () => {
        window.codeCopyManager = new CodeCopyManager();
    });
} else {
    window.codeCopyManager = new CodeCopyManager();
}