# Changelog

## 2026-04-07 — Pedagogical rewrite (article.tex/letter.tex primary)

### Source priority change
- All concept, definition, and result pages now cite article.tex and letter.tex as primary sources
- Free.tex (Notes) is only referenced for unitary/observable programming content (Sec. 7-9)
- Created paper overview pages: Letter.md, Article.md, Notes.md

### Batch 1: Major rewrites + core concept expansions (15 pages)
**Major rewrites** (previously cited Notes as primary with shallow content):
- `koashi-imoto.md` — Full 3-step proof of Prop 4 (Lagrange interpolation → orbit spans → bicommutant → Koashi-Imoto)
- `holevo-information.md` — Rewrote with Article converse role + unitary programming converse role, clarified Holevo χ vs free entropy χ notation
- `kumars-theorem.md` — Added geometric picture (corners of weight polytope), why multiplicity-one enables unique covariant channels, LR coefficient connection

**Core concept expansions** (pedagogical enrichment with proofs and examples):
- `free-entropy.md` — Worked qubit, qutrit, maximally-mixed examples; expanded "Why Free" section (Haar-random eigenbasis → freeness)
- `physical-free-entropy.md` — Full 4-step Appendix A derivation (Jacobian → Vandermonde → volume ratio → log); degenerate spectrum case; rank-deficient/pure-state cases
- `quantum-minimum-description-length.md` — Full achievability proof flow (Λ* construction, gap analysis, error split) + full converse proof flow (Haar-average, Markov, Koashi-Imoto per sector)
- `generalized-cloning-map.md` — Trace-preserving proof (Schur's lemma + trace), GL(3) example with 1-dim determinant ancilla, "why PRV" section
- `schur-weyl-duality.md` — Qubit (angular momentum) and qutrit (partition table) examples; how Schur transform acts on ρ^⊗n with weight decomposition
- `prv-component.md` — Worked GL(3) example, multiplicity-one consequences, LR coefficient connection
- `free-entropy-dimension.md` — Semicircular smearing derivation, spectral measure formula, 5 worked examples
- `vandermonde-determinant.md` — Full covering number computation role, eigenvalue repulsion, Weyl formula connection, factor-of-2 quantization story
- `weyl-dimension-formula.md` — Full 3-block asymptotic expansion derivation with term-by-term interpretation table
- `casimir-operator.md` — Full perturbation analysis: H=H₀+V decomposition, spectral gap, highest-weight trick, Davis-Kahan application
- `schumacher-compression.md` — "Two routes" narrative from Letter (typical subspaces vs typical matrices)
- `flag-manifold.md` — Dimensional counting, worked d=3 examples, KKS connection

### Batch 2: Result page proof expansions (15 pages)
Every result page now has a multi-step proof sketch following the actual paper argument:
- `cloning-fidelity.md` — 9-step proof: Stinespring → highest-weight Kraus → weight blocks → Davis-Kahan → determinantal ratio → tail → dimension → combine → reverse
- `achievability.md` — Full encoder/decoder with Λ* construction, gap analysis, error split, memory cost
- `converse.md` — 6-step proof: sector codes → Haar-average → Markov → good∩typical → Koashi-Imoto → Weyl dimension
- `kostka-monotonicity.md` — GT pattern injection (m'_{ij} = m_{ij} + ω_j), interlacing verification, Verma module equality argument
- `perturbation-lemma.md` — 5-step Casimir perturbation: H₀ eigenvalue, gap Θ(n), key E_α|ω⟩=0 trick, VP₀ bound, Davis-Kahan
- `probability-ratio.md` — Upper bound via Kostka, lower bound via determinantal Schur + rearrangement inequality + adjacent transposition exponents
- `tail-mass.md` — 4-step: individual weight bound, Kostant partition function, generating function, combination
- `remaining-lemmas.md` — All 9 mini-entries expanded with 2-5 sentences of proof detail
- `choi-matrix-lemma.md` — 5-step Choi-Jamiołkowski computation with intertwiner
- Programming results (6 pages): estimation-programming, sine-state, unitary converse, spectral achievability/converse, expectation achievability — all expanded

### Batch 3: Definition page expansions (14 pages)
Every definition page now has: concrete examples, expanded intuition, connection to proof architecture:
- Added qubit worked examples to: compression-code, generalized-cloning-map-def, free-entropy-voiculescu, physical-free-entropy-def, regularized-free-entropy, free-entropy-dimension-def, covariant-channel, edge-gap, normalized-gl-irrep, weight-space
- Added SSYT worked examples to kostka-number (5 examples)
- Added numerical example to typical-set (d=2, n=10000)
- Added geometric meaning to distance-between-irreps (3 worked examples)
- Expanded scaling-regime with natural-regime justification

### Batch 4: Remaining concept + open-question polish (20 pages)
- `sine-state.md` — Why sine state specifically (optimal Bayesian prior), Buzek-Derka-Massar connection
- `state-programming.md` — Compression vs programming table, adaptive strategy difficulty
- `kks-theorem.md` — Full Δ² vs Δ¹ explanation of the factor-of-1/2
- `kostant-partition-function.md` — Worked A₂ example, generating function formula
- `covering-numbers.md` — Ball-covering example, Kolmogorov-Tikhomirov connection
- `ych-scheme.md` — Full qubit protocol with encoding/decoding steps, J* choice, padding
- `werners-cloning-map.md` — Fidelity formula F=(n+1)/(m+1), optimality (Keyl-Werner)
- `free-probability-theory.md` — History (1983-2000s), free vs tensor products
- `young-diagrams.md` — ASCII diagram, hook-length formula with example
- `schur-transform.md` — Bacon-Chuang-Harrow implementation, spectrum estimation
- `petz-recovery-map.md` — DPI optimality, quantum error correction interpretation
- `gelfand-tsetlin-basis.md` — Concrete GL(3) GT pattern with weight computation
- Open questions (5 pages): all expanded with current thinking, difficulty analysis, and possible approaches
- `semicircular-element.md` — Density formula, Catalan moments, "why semicircular" explanation
- `observable-programming.md`, `unitary-programming.md` — Updated with result page links and coherent protocol

## 2026-04-07 — Initial wiki creation
- Ingested all three source files: `letter.tex`, `article.tex`, `Free.tex`
- Created concept pages: free-entropy, free-entropy-dimension, physical-free-entropy, schur-weyl-duality, generalized-cloning-map, prv-component, quantum-minimum-description-length, schur-polynomials, gelfand-tsetlin-basis, koashi-imoto, unitary-programming, observable-programming
- Created definition pages: free-entropy-voiculescu, physical-free-entropy, regularized-free-entropy, free-entropy-dimension, generalized-cloning-map, compression-code, scaling-regime
- Created result pages for all major theorems, lemmas, and propositions
- Created notation glossary
- Created open questions from author comments in Free.tex
- Created reference summaries for key cited works
- Built master index

## 2026-04-07 — Filled missing entries (audit pass)

### Definitions (14 new pages in `definitions/`)
- compression-code, generalized-cloning-map-def, free-entropy-voiculescu, physical-free-entropy-def, regularized-free-entropy, free-entropy-dimension-def, covariant-channel, scaling-regime, typical-set, edge-gap, normalized-gl-irrep, kostka-number, weight-space, distance-between-irreps

### Concepts (18 new pages in `concepts/`)
- werners-cloning-map, vandermonde-determinant, weyl-dimension-formula, flag-manifold, semicircular-element, free-probability-theory, young-diagrams, schur-transform, schumacher-compression, casimir-operator, sine-state, petz-recovery-map, kks-theorem, kostant-partition-function, covering-numbers, ych-scheme, state-programming, holevo-information, kumars-theorem

### Results (7 new pages in `results/`)
- estimation-programming-lemma, sine-state-programming, unitary-programming-converse, spectral-measurement-achievability, spectral-measurement-converse, observable-expectation-achievability, choi-matrix-lemma

### Paper stubs (3 new pages)
- Letter.md, Article.md, Notes.md — paper overview pages resolving broken wikilinks

### Fixes
- Removed 5 empty stub files (Article.md, Notes.md, etc. from initial pass)
- Fixed broken wikilink `[[references/key-references|Voiculescu's Free Entropy Papers]]` in free-entropy.md
- Added unitary/observable programming notation to notation.md (11 new symbols)
- Added representation theory extras to notation.md (10 new symbols)  
- Added random matrix / free probability notation to notation.md (5 new symbols)
- Rebuilt index.md: organized concepts by topic, added all new definitions/results tables, added programming dependency graphs
- Updated log.md
