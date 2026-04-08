# Introduction

> **Project:** "Free Entropy and Quantum Minimum Description Length"
> **Authors:** Patrick Hayden, Alexander Maloney, Jinzhao Wang, Yuxiang Yang

---

## What This Wiki Is

This is a structured, interlinked knowledge base covering every technical detail of the project on **free entropy and quantum minimum description length (QMDL)**. It is maintained by an LLM and designed to be browsed in [Obsidian](https://obsidian.md/) (all `[[wikilinks]]` are clickable). The raw source files (`.tex`, `.bib`) live in `sources/` and are never modified; everything else is derived from them.

## The Central Question

Given $n$ copies of a density matrix $\rho$ whose **spectrum is known** but whose **eigenbasis is not**, how much quantum memory do you need to store a faithful description of $\rho^{\otimes n}$?

This is fundamentally different from [[concepts/schumacher-compression|Schumacher compression]], which preserves purifications and costs $nS(\rho)$ qubits. Here we only need to recover the state itself (not its entanglement with a reference), so the cost is only $O(\log n)$ -- we are compressing a classical description of a continuous parameter (the eigenbasis).

## The Main Result

The optimal compression rate is governed by **Voiculescu's free entropy** -- a quantity from free probability theory that had no prior operational meaning in quantum information:

$$\log|M_n| = \frac{1}{2}\chi_{\mathrm{phy}}(\rho;\, n^{-1/2}) + \text{universal constants} + o(1)$$

Explicitly, for a rank-$r$ state with non-degenerate eigenvalues $x_1 > \cdots > x_r > 0$:

$$\log|M_n| = \underbrace{\frac{r(2d-r-1)}{2}\log n}_{\text{free entropy dimension}} + \underbrace{\sum_{i<j \leq r} \log(x_i - x_j) + (d-r)\sum_i \log x_i}_{\text{regularized free entropy}} - \sum_{k=d-r}^{d-1} \log k! + o(1)$$

The leading coefficient $r(2d-r-1)/2$ is the real dimension of the [[concepts/flag-manifold|flag manifold]] (the space of eigenbases), and the $O(1)$ correction encodes the eigenvalue repulsion -- larger spectral gaps make the state more compressible.

## The Three Papers

| Paper | Role | Key content |
|-------|------|-------------|
| **[[Letter]]** (`sources/letter.tex`) | PRL announcement | Defines physical free entropy, states the main QMDL result |
| **[[Article]]** (`sources/article.tex`) | Full journal paper | Complete proofs: generalized cloning map, achievability, converse |
| **[[Notes]]** (`sources/Free.tex`) | Extended working notes | All of the above + unitary & observable programming |

## Key Ideas at a Glance

### The Compression Protocol

1. Apply the [[concepts/schur-weyl-duality|Schur transform]] to decompose $\rho^{\otimes n}$ into irreducible sectors labeled by Young diagrams $\lambda$.
2. Discard the symmetric-group multiplicity (it carries no eigenbasis information).
3. Clone each sector's state into a single universal target irrep $\Lambda^*$ using the [[concepts/generalized-cloning-map|generalized cloning map]].
4. Store the result in a quantum memory of dimension $d_{\Lambda^*}$.

The converse uses the [[concepts/koashi-imoto|Koashi-Imoto structure theorem]] to show the orbit ensemble generates the full matrix algebra, forcing the memory to be at least $\log \dim \mathcal{H}_\lambda$.

### Beyond State Compression: Programming

The Notes extend the framework to **programming** -- storing a quantum program that implements an unknown unitary or observable:

- **[[concepts/unitary-programming|Unitary programming]]**: Cost $(f/2)\log(1/\varepsilon) + O(1)$, where $f$ is the number of free parameters.
- **[[concepts/observable-programming|Observable programming]]**: Cost $(d^2 \delta(H)/2)\log(1/\varepsilon) + O(1)$, where $\delta(H)$ is the [[concepts/free-entropy-dimension|free entropy dimension]].

The common thread: **free entropy governs the cost of storing classical descriptions of quantum objects**.

## How to Navigate

- **[[index]]** -- master table of contents with links to every page
- **[[notation]]** -- central glossary of all symbols
- **`concepts/`** -- one page per key concept (free entropy, Schur-Weyl duality, PRV component, ...)
- **`definitions/`** -- one page per formal definition
- **`results/`** -- one page per theorem/lemma, each with a **Main idea** summary and a detailed proof sketch
- **`open-questions/`** -- unresolved questions and conjectures
- **`references/`** -- annotated bibliography

Start with [[concepts/quantum-minimum-description-length|Quantum Minimum Description Length]] for the full story, or browse the [[index]] for a bird's-eye view.
