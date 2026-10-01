# Kolmogorov Complexity and Quantum Kolmogorov Complexity

**Appears in:** [[Letter]] (Discussion).

## Algorithmic Description Length

Kolmogorov complexity measures the length of a shortest program that produces an object on a chosen universal machine. Different universal machines change the complexity by an additive constant. This is a statement about individual objects and a computational description language.

For a fixed nonempty pattern $s$, the repeated string $s^n$ has description length $K(n)+O(1)=O(\log n)$: specify the pattern and the repeat count. One should not replace $K(n)$ by $\log n+O(1)$ for every $n$, since some integers have much shorter descriptions.

Minimum description length uses descriptions associated with a chosen statistical model class. It motivates the terminology of the project's compression task, but a name or analogy does not identify its operational cost with algorithmic complexity.

## Quantum Definitions

The Letter cites definitions of quantum Kolmogorov complexity by Berthiaume–van Dam–Laplante, Gács, and Müller. They use different computational or algorithmic-entropy frameworks. The Letter does not select one of these definitions or prove an equality with it.

In particular, a statement about the worst-case memory needed for an entire unknown-state family should not be read as a statement that every individual pure state has the same algorithmic complexity.

## The QMDL Analogy

The current Letter explicitly presents an analogy with quantum Kolmogorov complexity of the known-spectrum orbit family. Its [[concepts/quantum-minimum-description-length|QMDL]] is the optimal logarithm of memory dimension for CPTP codes that recover every member of that family with vanishing global error. The code may depend on the spectrum and $n$, but not on the unknown eigenbasis.

For distinct positive eigenvalues and rank $r$, the proved memory formula begins

$$|M_n|=\frac{r(2d-r-1)}2\log n+O(1).$$

The logarithmic scaling resembles describing a repeated classical pattern. Here, however, the unknown eigenbasis cannot be recorded exactly, and a classical estimate followed by preparation does not achieve the required vanishing global error. The retained description is quantum.

The exact compression formula is formalized in Lean. Equality with a machine-dependent notion of individual quantum description length, or a general computability theorem for QMDL, is not claimed. See [[proof-structure]].

## A Different Kolmogorov Quantity

Kolmogorov $\varepsilon$-entropy is the logarithm of a [[concepts/covering-numbers|covering number]] in a metric space. It is distinct from algorithmic complexity. The Letter's physical free entropy uses a volume ratio that agrees with a covering entropy up to a bounded term at fixed dimension; its precise additive constant comes from the volume convention.

## Related

- [[concepts/quantum-minimum-description-length|Quantum Minimum Description Length]]
- [[concepts/physical-free-entropy|Physical Free Entropy]]
- [[concepts/covering-numbers|Covering Numbers]]

## References

- `rissanen1978modeling`: Rissanen, "Modeling by shortest data description" (1978).
- `Berthiaume_2001`: Berthiaume, van Dam, and Laplante, "Quantum Kolmogorov complexity" (2001).
- `G_cs_2001`: Gács, "Quantum algorithmic entropy" (2001).
- `mueller2007`: Müller, "Quantum Kolmogorov complexity and the quantum Turing machine" (2007).
