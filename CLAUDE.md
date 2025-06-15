# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Build Commands

- **Compile main document**: `latexmk -pdf main.tex`
- **Create AI bundle**: `python bundle.py` (generates ai_bundle.tex containing all .tex files)
- **Clean build artifacts**: `latexmk -c` or `rm -rf build/`

## Repository Architecture

This is a mathematical LaTeX document repository developing "Golden Algebra" theory. The content is organized hierarchically:

### Document Structure
- `main.tex` - Primary entry point that includes all components
- `postulates.tex` - Standalone document defining foundational postulates
- `preamble.tex` - LaTeX packages, custom commands, and theorem environments
- Build outputs go to `build/` directory via `.latexmkrc` configuration

### Content Organization
The mathematical content follows a three-tier structure:

1. **Definitions** (`compendium/defs/`) - Brief law/operator definitions
2. **Compendium** (`compendium/`) - Summary pages that load definitions and provide overview
3. **Detailed Chapters** - Full theorems, proofs, and examples

Key directories:
- `compendium/laws-of-harmony-and-dynamics/` - Detailed law chapters
- `compendium/operators/` - Operator theorems and properties
- `images/` - Figures organized by topic (compendium/, operators/)

### Content Loading Pattern
- Definitions are loaded first via `core.tex`, `operators.tex`, and `laws.tex`
- The compendium references definitions using custom `\GetLaw{}` commands
- Detailed chapters provide full mathematical development

### Important Notes
- PDFs (main.pdf, ai_bundle.pdf, postulates.pdf) are tracked in version control
- When adding new mathematical content, follow the three-tier pattern
- Place new definitions in appropriate `defs/` subdirectory
- Update corresponding loader file (core.tex, operators.tex, or laws.tex)