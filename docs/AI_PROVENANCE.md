# AI assistance and process record

This document reports the process supported by the available working
record. It separates mathematical authorship, formalization assistance,
verification, and review. It is a concise methods summary, not a complete
session transcript.

## Source and task selection

The user supplied `article.tex` and asked to formalize its Theorems 1 and 2.
The source manuscript is *Quantum minimum description of density matrices*,
by Patrick Hayden, Alexander Maloney, Jinzhao Wang, and Yuxiang Yang.
The existing manuscript was the mathematical source; the AI was asked to
produce formal certificates and close proof obligations. This record does
not claim the AI originated the manuscript's results or arguments.

This release concerns one user-selected manuscript and two target theorems.
It is not a reported benchmark or a selected sample from a documented
collection of attempted research problems. No broader success rate can be
inferred from it.

## Human instructions recorded in the conversation

The following are selected user instructions, with the supplied file
referred to by its repository-relative name:

> make your best effort to lean formalize the proof of theorem 1 and theorem 2.

> try to close the gaps on the conditional claims

> KEEP PUSHING

> keep going, close all the gaps

> close the rest gaps

The later release request asked for organization following `openai/ten-proofs`
and the September 29, 2026 AGMAI guideline, in preparation for a future
GitHub repository. A subsequent instruction explicitly requested publication
to `https://github.com/JWang226/QMDL`, preserving that repository's existing
wiki, with README reproduction instructions for Lean, Comparator, and Nanoda.
The repository was subsequently renamed to
[Quantum-Minimum-Description-Length](https://github.com/JWang226/Quantum-Minimum-Description-Length);
the historical publication request above retains its original destination.

## Tools and automation

- Framework: Codex, with a primary agent and collaborating agents.
- Proof environment: the exact Lean toolchain and Mathlib revision in
  `lean/lean-toolchain` and `lean/lake-manifest.json`.
- Proof work: Lean source generation and revision, compilation feedback,
  library searches, and independent agent reviews of the final statements.
- Verification: the Lean kernel and the transitive-axiom audit in
  `lean/audit.py`; Comparator challenges and their separate status are
  documented in `lean/ComparatorChallenges/README.md`.
- Release organization: source mapping, provenance records, headers,
  pinned metadata schema, validation, CI configuration, and an explicit
  source-release allowlist.

The exact deployed model identifier was not independently captured in the
release evidence. It is therefore recorded as unavailable rather than
inferred from an interface label. Total computation cost, tokens, wall-clock
duration, and hardware allocation were likewise not reliably recorded.
The dates on generated files are not estimates of total research effort.

## Methods summary

The development first separated scalar/asymptotic reductions from the
finite-dimensional quantum and representation-theoretic inputs. The
subsequent work supplied those inputs inside Lean: actual matrix channels,
tensor-source decompositions, highest-weight models, dimension formulas,
weight and concentration estimates, and source-transfer bounds.

The final construction connects the actual physical tensor-source codes to
the precise memory expression and both uniform and Haar-average error
criteria. The cloning statement was then connected to the manuscript's
original Choi-projector formulas in both directions, with highest-weight,
cyclicity, multiplicity-one, normalization, covariance, zero-increment,
and Petz-recovery identities proved. See `lean/README.md` for the module
map and `metadata/natural-language-map.json` for exact source references.

Earlier conditional lemmas remain reusable intermediate results. Their
extra representation and error premises are discharged in the final
theorem statements. They are not advertised as standalone unconditional
versions of the manuscript's conclusions.

## Review and unavailable evidence

The working record contains agent reviews comparing the final statements
and definitions with the manuscript. It does not establish an independent
human expert review, author sign-off, journal peer review, or an external
certification of the entire manuscript. Lean checks the precise formal
statements; mathematical review of their fidelity to the source remains a
separate responsibility.

The release includes final sources and generated verification evidence.
It does not contain a complete replayable record of every model call,
intermediate draft, or abandoned attempt. Missing provenance fields are
explicitly marked rather than reconstructed from guesses.

## References

- [Responsible Release of AI-Generated Mathematics](https://agmai.org/general-sep29/)
- [ten-proofs repository](https://github.com/openai/ten-proofs)
- [formalization.yaml standard](https://github.com/mathlib-initiative/formalization.yaml)
