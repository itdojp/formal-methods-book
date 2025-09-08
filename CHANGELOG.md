# Changelog

All notable changes to this book-publishing-template will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Added
- CHANGELOG.md to track template changes and improvements
- Status indicators in README.md for template integration tracking
- Template version tracking system
- index.md template for better content generation
- Custom index.md support from project root

### Changed
- README.md structure improved with better organization
- Enhanced documentation for template usage
- Navigation addition logic for introduction/afterword sections (now skipped by default)
- index.md generation now properly uses author information from book-config.json

### Fixed
- Introduction and afterword sections no longer get duplicate navigation
- Author name properly displayed in generated index.md
- Better handling of custom index.md files

## Template Integration Checklist

When integrating this template into a book project, track your progress:

✅ **GitHub Actions**: Latest workflow configurations  
✅ **Build System**: PDF/EPUB support, content validation  
✅ **Configuration**: Spell checking, Japanese text linting  
✅ **Documentation**: Comprehensive setup guides  
✅ **Security**: Proper token management and permissions  

## Template Usage Notes

This template provides:
- 🚀 **Single Repository System**: Simple setup with GitHub Pages from /docs folder
- 📝 **Markdown-based**: Write in Markdown with full LaTeX math support
- 🎨 **Beautiful Output**: Clean, responsive design with syntax highlighting
- 🔧 **Incremental Builds**: Fast rebuilds by processing only changed files
- 🔒 **Private Content**: Automatic filtering of private comments and drafts
- 🌍 **Multi-platform**: GitHub Pages, Zenn, and Kindle support

## Migration History

Record your template integration steps here for future reference and troubleshooting.