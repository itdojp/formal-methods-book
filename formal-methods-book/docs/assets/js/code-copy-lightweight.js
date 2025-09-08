/**
 * Lightweight Code Copy Functionality
 * Minimal implementation for better performance
 */

(function() {
    'use strict';
    
    // Wait for DOM to be ready
    if (document.readyState === 'loading') {
        document.addEventListener('DOMContentLoaded', initCodeCopy);
    } else {
        initCodeCopy();
    }
    
    function initCodeCopy() {
        // Find all code blocks
        const codeBlocks = document.querySelectorAll('pre code, .highlight code');
        
        codeBlocks.forEach(addCopyButton);
    }
    
    function addCopyButton(codeBlock) {
        const pre = codeBlock.closest('pre') || codeBlock.parentElement;
        if (!pre) return;
        
        // Skip if copy button already exists
        if (pre.querySelector('.copy-button')) return;
        
        // Create copy button
        const copyButton = document.createElement('button');
        copyButton.className = 'copy-button';
        copyButton.innerHTML = 'Copy';
        copyButton.setAttribute('aria-label', 'Copy code to clipboard');
        
        // Add click handler
        copyButton.addEventListener('click', () => copyCode(codeBlock, copyButton));
        
        // Style the container
        if (pre.style.position !== 'relative') {
            pre.style.position = 'relative';
        }
        
        // Add button to pre element
        pre.appendChild(copyButton);
    }
    
    async function copyCode(codeBlock, button) {
        const code = codeBlock.textContent || codeBlock.innerText;
        
        try {
            if (navigator.clipboard && navigator.clipboard.writeText) {
                await navigator.clipboard.writeText(code);
            } else {
                // Fallback for older browsers
                fallbackCopyToClipboard(code);
            }
            
            showCopySuccess(button);
        } catch (err) {
            console.warn('Failed to copy code:', err);
            showCopyError(button);
        }
    }
    
    function fallbackCopyToClipboard(text) {
        const textArea = document.createElement('textarea');
        textArea.value = text;
        textArea.style.position = 'absolute';
        textArea.style.left = '-9999px';
        document.body.appendChild(textArea);
        textArea.select();
        document.execCommand('copy');
        document.body.removeChild(textArea);
    }
    
    function showCopySuccess(button) {
        const originalText = button.innerHTML;
        button.innerHTML = 'Copied!';
        button.classList.add('copied');
        
        setTimeout(() => {
            button.innerHTML = originalText;
            button.classList.remove('copied');
        }, 2000);
    }
    
    function showCopyError(button) {
        const originalText = button.innerHTML;
        button.innerHTML = 'Error';
        button.classList.add('error');
        
        setTimeout(() => {
            button.innerHTML = originalText;
            button.classList.remove('error');
        }, 2000);
    }
})();