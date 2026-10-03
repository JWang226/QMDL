# Memory Bound for Irreducible Compact-Group Orbits

**Label:** `prop:compact_orbit_memory`, `eq:compact_orbit_memory` in the current [[Article]].
**Source:** [Article proposition and proof](https://github.com/JWang226/Quantum-Minimum-Description-Length/blob/main/article.tex#L854).
**Lean theorem:** [FreeEntropy.OrbitTraceDistance.irreducible_orbit_memory_bound](https://github.com/JWang226/Quantum-Minimum-Description-Length/blob/main/lean/FreeEntropy/OrbitTraceDistance.lean#L180).

## Statement

Let $U:G\to\mathcal U(\mathcal H)$ be a continuous irreducible representation of a compact group, with normalized Haar measure. Let $\tau$ be a density matrix with a simple largest eigenvalue $p_0$ and corresponding rank-one projector $P$. Write

$$
p_1=\|(I-P)\tau(I-P)\|_\infty,\qquad
\gamma=p_0-p_1>0,\qquad
\tau_g=U(g)\tau U(g)^\dagger.
$$

For arbitrary CPTP maps $\mathcal E:\mathcal B(\mathcal H)\to\mathcal B(M)$ and $\mathcal D:\mathcal B(M)\to\mathcal B(\mathcal H)$, set

$$
\overline\delta=\int_G\frac12\|\mathcal D\mathcal E(\tau_g)-\tau_g\|_1\,dg.
$$

Then

$$
\dim M\ge\dim\mathcal H\left(1-\frac{\overline\delta}{\gamma}\right).
$$

The right side may be nonpositive at large error; the useful regime is $\overline\delta<\gamma$. The bound concerns dimensions, not logarithmic costs.

## Intuition

The orbit of the highest-eigenvalue projector averages to $I/\dim\mathcal H$. Testing the recovered states against these projectors relates average recovery quality to how much operator mass can pass through the memory. The gap $\gamma$ turns that test into a quantitative bound on memory dimension.

At zero error this gives exact incompressibility. For vanishing error across changing representations, a gap bounded away from zero is what preserves the additive logarithmic memory constant.

## Proof Sketch

Let $\Phi=\mathcal D\circ\mathcal E$ and $P_g=U(g)PU(g)^\dagger$. Positivity and trace preservation give $\mathcal E(P_g)\le I_M$. The spectral bound $\tau_g\le p_1I+\gamma P_g$ therefore implies

$$
\Phi(\tau_g)\le p_1\Phi(I)+\gamma\mathcal D(I_M).
$$

Irreducibility and normalized Haar invariance give the twirling identity

$$
\int_G P_g\,dg=\frac{I}{\dim\mathcal H}.
$$

A rank-one projection is an effect, so trace distance bounds the change in its expectation. Testing and averaging yields

$$
\begin{aligned}
p_0-\overline\delta
&\le\int_G\operatorname{Tr}[P_g\Phi(\tau_g)]\,dg\\
&\le\frac{p_1\operatorname{Tr}\Phi(I)+\gamma\operatorname{Tr}\mathcal D(I_M)}
{\dim\mathcal H}
=p_1+\gamma\frac{\dim M}{\dim\mathcal H}.
\end{aligned}
$$

Rearrange to obtain the result. Complete positivity is more than this particular inequality needs: the generic Lean lemma uses positive trace-preserving real-linear maps, and is then applied to the actual CPTP channels.

## Canonical States and the Uniform Gap

For the actual canonical states used in [[results/converse|Theorem 1]], the checked route proves

$$
q_x=\max_{i<r}\frac{x_{i+1}}{x_i}<1,\qquad
\gamma\ge\gamma_*=(1-q_x)^{\binom d2+1}>0,
$$

where $q_x=0$ for rank one. This follows from the simple highest line and the proved weight-counting envelope, uniformly in the highest row. The theorem [FreeEntropy.ExteriorRepresentation.canonical_orbit_memory_bound](https://github.com/JWang226/Quantum-Minimum-Description-Length/blob/main/lean/FreeEntropy/CanonicalOrbit.lean#L73) supplies the resulting bound without assuming a gap or a counting estimate.

The Article's [uniform-gap lemma](https://github.com/JWang226/Quantum-Minimum-Description-Length/blob/main/article.tex#L901) states the sharper constant $(1-q_x)\prod_{i<j\le r}(1-x_j/x_i)$. The final canonical endpoint above uses $\gamma_*$, which suffices for the main converse. Distinct eigenvalues of the original spectrum imply the required simple **largest** eigenvalue; they do not require every eigenvalue of the representation state to be distinct.

## Lean Map

- [FreeEntropy.Twirling.compact_trace_one_unitary_twirl](https://github.com/JWang226/Quantum-Minimum-Description-Length/blob/main/lean/FreeEntropy/Twirling.lean#L190): Haar averaging from actual continuity, unitarity, and irreducibility.
- [FreeEntropy.OrbitEigenvalues.irreducible_orbit_memory_bound_of_eigenvalues](https://github.com/JWang226/Quantum-Minimum-Description-Length/blob/main/lean/FreeEntropy/OrbitEigenvalues.lean#L34): constructs the projector from Hermitian eigenvalue data.
- [FreeEntropy.CartanLieCloning.CyclicWeightModel.actual_uniform_gap](https://github.com/JWang226/Quantum-Minimum-Description-Length/blob/main/lean/FreeEntropy/CyclicWeightOrbit.lean#L53): the uniform positive gap used by the canonical specialization.

The generic theorem explicitly states its representation and spectral assumptions. The final Theorem 1 constructs and verifies these inputs. The old wiki's argument through exact [[concepts/koashi-imoto|Koashi–Imoto]] structure is historical context, not a substitute for this quantitative approximate-recovery estimate.

## Dependencies

- Schur's lemma and normalized Haar integration
- Spectral decomposition and positivity
- [[definitions/compression-code|Encoding and decoding channels]]
- Trace-distance expectation bounds

## Used By

- [[results/converse|Theorem 1 converse]], after transferring the physical code to the padded target orbit
