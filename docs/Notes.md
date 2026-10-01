# Extended Notes

**Title:** "Free entropy and quantum minimum description length"
**Authors:** Patrick Hayden, Alexander Maloney, Jinzhao Wang, Yuxiang Yang
**Format:** Extended working notes (JHEP style)
**File:** `sources/Free.tex`

## Summary

These are extended working notes from the earlier wiki source snapshot. They contain an earlier state-compression proof and additional programming topics:
- [[open-questions/free-entropy-conjecture|Programming Extensions]] (Secs. 7-9: state programming, unitary programming, observable programming)

The current [[Article]] and [[proof-structure|Lean proof structure]] supersede the older fidelity-based compression route described here. The current [[Letter]] also supersedes the Notes' earlier physical-entropy conventions: it defines a tube-volume ratio and uses resolution $n^{-1}$ in the half-entropy relation. In particular, the current direct trace-distance estimate proves $O(\log n/\sqrt n)$ reconstruction error. Historical working comments are not evidence of an unresolved gap in those endpoints; see [[open-questions/error-scaling|the remaining error-tradeoff questions]].

## Sections

1. Introduction
2. Defining free entropy in finite dimensions
3. Free entropy of density operators: quantum state compression
4. Estimating the generalized cloning fidelity
5. Achievability for qudits
6. Converse
7. The visible setting: programming quantum states
8. Free entropy of unitary operators: unitary programming
9. Free entropy of Hermitian operators: observable programming

## Unique Results (not in Article)

- See [[open-questions/free-entropy-conjecture|Programming Extensions]] for all results from Secs. 7-9 (estimation-programming lemma, sine-state programming, unitary programming converse, spectral measurement programming, observable expectation programming)
