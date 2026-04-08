# Wiki Schema & Maintenance Instructions

This is a **Karpathy-style LLM-maintained wiki** for the project "Free Entropy and Quantum Minimum Description Length" by Hayden, Maloney, Wang, and Yang.

## Purpose

Help the authors and collaborators understand all technical details of the papers. The wiki should be consultable for any concept, result, or proof technique used in the project.

## Source Files

All raw `.tex` and `.bib` files live in `sources/`. These are the ground truth. **Never modify source files.**

- `sources/letter.tex` — PRL letter: "Free entropy and quantum minimum description length" (short announcement)
- `sources/article.tex` — Full paper: "Quantum minimum description of density matrices" (companion with full proofs)
- `sources/Free.tex` — Extended working notes with full proofs + unitary/observable programming
- `sources/free.bib` — Shared bibliography
- `sources/compression.pdf` — Compression figure

## Directory Structure

```
free-entropy-wiki/
  CLAUDE.md          — This file (schema + LLM instructions)
  index.md           — Master table of contents with links to everything
  log.md             — Changelog (append-only)
  notation.md        — Central notation glossary
  sources/           — Raw .tex/.bib (immutable)
  concepts/          — One page per key concept (free entropy, Schur-Weyl, PRV, ...)
  definitions/       — One page per formal definition
  results/           — One page per theorem/lemma/proposition/corollary
  open-questions/    — Unresolved questions and conjectures
  references/        — One page per key cited paper with relevance summary
```

## Page Templates

### Concept Page (`concepts/`)
```markdown
# <Concept Name>
**Appears in:** [[paper references]]
## Intuition
Plain-language explanation.
## Formal Description
LaTeX-rendered formal content.
## Role in the Project
Why this concept matters for the papers.
## Related
- [[links to definitions, results, other concepts]]
```

### Definition Page (`definitions/`)
```markdown
# <Definition Name>
**Label:** `\label{...}` in source
**Source:** [[which .tex file]], line ~N
## Statement
Formal definition in LaTeX.
## Intuition
What it means informally.
## Examples
Concrete instances.
## Used By
- [[results that invoke this definition]]
```

### Result Page (`results/`)
```markdown
# <Result Name> (Theorem/Lemma/Proposition N)
**Label:** `\label{...}` in source
**Source:** [[which .tex file]], line ~N
## Statement
Formal statement in LaTeX.
## Intuition
What it says in plain language.
## Proof Sketch
High-level proof strategy.
## Dependencies
- [[definitions and results this depends on]]
## Used By
- [[results that cite this one]]
## Key Equations
Important intermediate equations.
```

### Open Question Page (`open-questions/`)
```markdown
# <Question>
**Source:** [[which .tex file]], line ~N
**Status:** Open / Partially resolved / Resolved
## Context
Why this question arises.
## Current Thinking
What the authors have tried or conjectured.
## Related
- [[links]]
```

## Maintenance Workflow

### On Ingest (new/updated source)
1. Diff against previous version in `sources/`
2. Update or create pages for every new/changed definition, result, concept
3. Update cross-references (`## Dependencies`, `## Used By`)
4. Update `notation.md` for any new symbols
5. Update `index.md`
6. Append to `log.md`

### On Query
1. Search relevant wiki pages
2. Synthesize answer with `[[links]]` to wiki pages
3. If the answer reveals a gap, create a new page or update existing ones

### On Lint
1. Check for broken `[[links]]`
2. Check for results missing `## Dependencies` or `## Used By`
3. Check for orphaned pages (not linked from anywhere)
4. Check for stale content (source has changed but wiki page hasn't)
5. Verify `notation.md` is complete

## Conventions

- Use `[[wikilinks]]` (Obsidian-style) for internal cross-references
- LaTeX math: use `$...$` for inline, `$$...$$` for display
- Eigenvalues of $\rho$: always $p_1 > p_2 > \cdots > p_r > 0$ (or $x_1 > \cdots > x_r > 0$ in article.tex)
- Partitions/Young diagrams: $\lambda = (\lambda_1 \ge \lambda_2 \ge \cdots \ge \lambda_d)$
- The three papers are referred to as **Letter**, **Article**, and **Notes**
