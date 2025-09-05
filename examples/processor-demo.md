---
title: Processor Demo
author: Book Template
date: 2024
---

# {{var:title}}

This document demonstrates the custom processor system.

## Variable Replacement

- Author: {{var:author}}
- Year: {{var:year}}
- Date: {{var:date}}

## File Inclusion

Below is included content:

{{include:examples/sample-include.md}}

## Code Execution

```javascript:exec
const numbers = [1, 2, 3, 4, 5];
const sum = numbers.reduce((a, b) => a + b, 0);
return `Sum of ${numbers.join(', ')} = ${sum}`;
```

## CSV Tables

```csv
Feature,Status,Priority
Variable Replacement,✅ Complete,High
File Inclusion,✅ Complete,High
Code Execution,✅ Complete,Medium
CSV Tables,✅ Complete,Medium
Emoji Support,🚧 In Progress,Low
```

## Emoji Support

Common emojis:
- :smile: Happy coding!
- :rocket: Fast builds
- :books: Great documentation
- :white_check_mark: All tests passing
- :fire: Hot features

## Links

- [Internal Link](./internal-page.md)
- [External Link](https://example.com)
- [GitHub](https://github.com)

## Advanced Features

### Nested Includes

You can include files that include other files (up to configured depth).

### Custom Variables

Environment variables with prefix `VAR_` are automatically available:
- VAR_BUILD_ENV = {{var:BUILD_ENV}}

### Glossary Terms

When the glossary processor is enabled, technical terms like API, REST, and JSON
will automatically be linked to their definitions.

## Summary

The processor system provides:
1. Extensible architecture
2. Chainable processors
3. Custom transformations
4. Error handling
5. Performance optimization

Happy writing! :sparkles: