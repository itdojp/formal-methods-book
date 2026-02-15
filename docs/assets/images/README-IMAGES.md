# README.md Images

This file documents the images that should be created for the README.md GitHub configuration steps.

## Required Images

### 1. ✅ book-publishing-template-use-this.png (Available)
**Description:** Screenshot of GitHub repository page showing the "Use this template" button
**Content:**
- Repository header with "Use this template" button highlighted with red circle
- Shows the green "Use this template" button clearly
- Actual size: Optimized for web display

### 2. ✅ book-publishing-template-repository-name.png (Available)
**Description:** Screenshot of the "Create a new repository" form
**Content:**
- Repository template selection showing "itdojp/book-publishing-template"
- Repository name field highlighted with red circle
- Public/Private radio buttons with Private selected
- Description field visible
- "Create repository" button at bottom
- Actual size: Optimized for web display

### 3. github-pages-settings.png
**Description:** Screenshot of GitHub Pages settings in repository settings
**Content:**
- Settings tab navigation
- Pages section in left sidebar
- Source configuration showing "Deploy from a branch"
- Branch selection dropdown with "gh-pages" selected
- Save button
- Recommended size: 1000x700px

### 4. github-actions-setup.png
**Description:** Screenshot of GitHub Actions workflow tab
**Content:**
- Actions tab in repository navigation
- Example workflow run showing successful deployment
- Green checkmark indicating successful build
- Workflow name like "Deploy to GitHub Pages"
- Recommended size: 900x500px

## Image Guidelines

### Technical Requirements
- Format: PNG (for screenshots)
- Compression: Optimized for web (< 500KB per image)
- Resolution: High enough for clarity on retina displays
- Color space: sRGB

### Visual Guidelines
- Use browser with clean interface (Chrome/Firefox)
- Include relevant context but crop unnecessary UI
- Highlight important buttons/sections with subtle borders or arrows
- Use consistent browser zoom level across screenshots
- Ensure text is readable at small sizes

### Accessibility
- Include descriptive alt text in markdown
- Use caption text below images to explain the action
- Ensure sufficient contrast in highlighted areas

## Taking Screenshots

### Recommended Tools
- **macOS:** Shift+Cmd+4 for selection screenshots
- **Windows:** Snipping Tool or Snip & Sketch
- **Linux:** GNOME Screenshot or Spectacle
- **Cross-platform:** LightShot, Greenshot

### Browser Setup
1. Use a clean browser profile
2. Set zoom to 100% or 110%
3. Hide personal information (usernames, etc.)
4. Use placeholder repository names like "my-book-template"

### GitHub Theme
- Use GitHub's default light theme for consistency
- Avoid dark mode for better print compatibility
- Ensure good contrast for all UI elements

## File Naming Convention

```text
assets/images/github-[action]-[detail].png
```

Examples:
- `github-use-template.png`
- `github-create-repo.png` 
- `github-pages-settings.png`
- `github-actions-setup.png`

## Updating Images

When GitHub updates their UI:
1. Take new screenshots following the same guidelines
2. Ensure all referenced elements are still visible
3. Update alt text if UI text has changed
4. Test image loading in README preview
5. Commit with descriptive message about UI changes

## Alternative Solutions

If screenshots become outdated or maintenance-intensive:

### Option 1: Diagrammatic Approach
Create simplified diagrams showing the workflow instead of actual screenshots

### Option 2: Text-based Instructions
Provide detailed text instructions with code samples for navigation

### Option 3: Video Tutorial
Create a short video walkthrough hosted on the repository

### Option 4: External Documentation
Link to comprehensive setup guide with maintained screenshots

## Notes for Contributors

When adding or updating images:
1. Test image display in both light and dark GitHub themes
2. Verify images are accessible to screen readers
3. Ensure images work in both web and mobile GitHub views
4. Consider file size impact on repository clone time
5. Add appropriate alt text for accessibility

---

**Next Steps:**
1. Take screenshots following the guidelines above
2. Optimize images for web delivery
3. Add them to the assets/images/ directory
4. Verify display in README.md preview
5. Update this documentation if changes are needed