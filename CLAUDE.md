# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

This is "Mirror Math and Golden Algebra" by Tristen Harr with Gemini 2.5 Pro Preview as Computational Partner. The repository develops a novel mathematical framework around golden ratio properties, with extensive symbolic validation.

## Build Commands

- **Compile main document**: `latexmk -pdf main.tex`
- **Compile postulates document**: `latexmk -pdf postulates.tex`
- **Create AI bundle**: `python bundle.py` (generates ai_bundle.tex containing all .tex files, excluding `applications/`, `build/`, and `.git/`)
- **Compile AI bundle**: `latexmk -pdf ai_bundle.tex`
- **Clean build artifacts**: `latexmk -c` or `rm -rf build/`
- **View compilation logs**: Check `build/main.log` or `build/postulates.log` for detailed error messages
- **Force recompile**: `latexmk -g -pdf main.tex` (useful if latexmk doesn't detect changes)

## Repository Architecture

This is a mathematical LaTeX document repository developing "Golden Algebra" theory. The content is organized hierarchically:

### Document Structure
- `main.tex` - Primary entry point that includes all components
- `postulates.tex` - Standalone document defining foundational postulates
- `preamble.tex` - LaTeX packages, custom commands, and theorem environments
- Build outputs go to `build/` directory via `.latexmkrc` configuration

### Content Organization
The mathematical content follows a three-tier structure:

1. **Definitions** (`compendium/defs/`) - Brief law/operator definitions using `\NewLaw{name}{definition}` macro
2. **Compendium** (`compendium/compendium.tex`) - Summary page that loads definitions and provides overview
3. **Detailed Chapters** - Full theorems, proofs, and examples in dedicated .tex files

Key directories:
- `compendium/laws-of-harmony-and-dynamics/` - Detailed law chapters
- `compendium/operators/` - Operator theorems and properties  
- `images/` - Figures organized by topic (compendium/, operators/)
- `applications/` - Applied examples (excluded from ai_bundle.tex)

### Content Loading Pattern
- Definitions are loaded via loader files:
  - `compendium/core.tex` - Core foundation definitions
  - `compendium/operators/operators.tex` - All operator definitions
  - `compendium/laws-of-harmony-and-dynamics/laws.tex` - All law definitions
- The compendium references definitions using custom `\GetLaw{name}` commands
- Detailed chapters provide full mathematical development
- Each law/operator follows naming pattern: `law-name-def.tex` (definition) and `law-name.tex` (detailed)

### Key Custom Macros
- `\NewLaw{name}{definition}` - Stores law definitions
- `\GetLaw{name}` - Retrieves stored definitions
- `\gold` - Golden ratio (φ)
- `\LambdaG` - Dampening operator (Λ_{G1})
- `\PiA` - Projection operator (Π_A)
- `\DissonanceVector` - Dissonance vector notation
- `\MetricInvariant` - Metric invariant notation
- Additional operators defined in preamble.tex

### Document Entry Points
- `titlepage.tex` - Title page with author and collaborative partner info
- `main.tex` - Includes all components in order: preamble → titlepage → compendium → core foundations → detailed chapters → appendix
- `postulates.tex` - Standalone document with foundational postulates only

### Mathematical Validation

- `appendix.tex` contains extensive symbolic validation of 207+ Golden Algebra properties
- All validations performed using SymPy for exact symbolic mathematics
- Properties span: fundamental constants, self-referential relations, trigonometry, matrices, Fibonacci-Lucas connections, elliptic curves
- Each validation marked as "Rigorously Proven" with symbolic expressions

### Important Notes
- PDFs and `.synctex.gz` files (for PDF synchronization) are tracked in version control
- When adding new mathematical content, follow the three-tier pattern
- Place new definitions in appropriate `defs/` subdirectory
- Update corresponding loader file (core.tex, operators.tex, or laws.tex)
- Use kebab-case for file naming (e.g., `harmonic-stability-def.tex`)
- The `applications/` directory exists but is currently empty (reserved for future use)
- The compendium refers to itself as "The Mirror Math Spell-Book"