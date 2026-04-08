# Open: Converse for Visible Setting (State Programming)

**Source:** Notes, line ~1463
**Status:** Open

## Context

Section 7 of the Notes discusses the "visible setting" where you want to prepare a program state $|\pi_\rho\rangle$ that, together with a fixed universal processor, outputs $\rho^{\otimes n}$ approximately. This is closely related to state compression but formulated as a programming task.

## Question

How to prove the converse (lower bound) for the visible state programming setting? The achievability follows from the compression result, but the converse requires a different argument.

## The Difficulty: Adaptive Strategies

In the **blind** (compression) setting, the converse is proved using the [[concepts/schur-weyl-duality|Schur-Weyl Duality]] structure: the encoder is a single fixed channel $\mathcal{E}$, and Schur's lemma constrains what it can do. The Holevo information argument bounds the mutual information between the encoded state and the unitary parameter $g$, yielding the lower bound.

In the **visible** (programming) setting, the encoder *knows* $\rho$ classically and can use a **different encoding for each $\rho$**. This extra power creates two obstacles for proving a converse:

1. **No single-channel constraint:** The blind converse relies on the encoder being a single CPTP map $\mathcal{E}$ applied to $\rho^{\otimes n}$. In the visible setting, the mapping $\rho \mapsto \sigma_\rho$ (program state) can be an arbitrary function, not necessarily coming from a quantum channel. This breaks the Holevo information argument.

2. **Adaptive strategies:** The visible encoder could in principle use entirely different strategies for different regions of state space. For instance, it could use a different basis of program states for states near $\rho_1$ vs. states near $\rho_2$, with no requirement of continuity or covariance. Proving that such adaptive strategies cannot beat blind compression is the core difficulty.

**A possible approach** (suggested in the Notes): First show that the decoder $\mathcal{D}$ can be assumed covariant without loss of generality (by averaging over the unitary group). Then the covariance of $\mathcal{D}$ combined with Schur's lemma would constrain the program states $\sigma_\rho$, potentially reducing the problem to the blind case. The key step is showing that covariantizing $\mathcal{D}$ does not hurt the programming rate.

## Related

- [[concepts/quantum-minimum-description-length|Quantum Minimum Description Length]]
- [[results/converse|Converse (State Compression)]]

## External References

- [Koashi and Imoto, "Compressibility of quantum mixed-state signals" (2001)](https://arxiv.org/abs/quant-ph/0101144)
- [Schur-Weyl duality (Wikipedia)](https://en.wikipedia.org/wiki/Schur%E2%80%93Weyl_duality)
