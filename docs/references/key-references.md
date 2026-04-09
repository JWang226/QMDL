# Key References

Summary of the most important cited works and their relevance to the project.

---

## Voiculescu's Free Entropy Series (1993-2002)

- **voiculescu1993analogues** (I): Introduced free entropy $\chi(a)$ for single self-adjoint variables. Defined microstate free entropy via volumes of matrix approximants.
- **voiculescu1994analogues** (II): Extended to several variables. Introduced free Fisher information.
- **voiculescu1996analogues** (III): Applied to prove absence of Cartan subalgebras in free group factors. Major application to operator algebras.
- **voiculescu1998analogues** (V): Non-commutative Hilbert transforms and free entropy.
- **voiculescu1999analogues** (VI): Liberation and mutual free information.
- **voiculescu2002free**: Survey article on free entropy. [doi:10.1112/S0024609301008992](https://doi.org/10.1112/S0024609301008992)

**Relevance:** The mathematical foundation. This project gives Voiculescu's free entropy its first operational/physical interpretation.

---

## Hiai-Petz (2000)

- **hiai2000semicircle**: *The Semicircle Law, Free Random Variables and Entropy* (book)
- **hiai1998maximizing**: Maximizing free entropy
- **hiai2005large**, **hiai2006notes**, **hiai2006log**: Free entropy of projections

**Relevance:** Provides the explicit formulas for free entropy used in the project. The Hiai-Petz book is the standard reference for computational aspects of free entropy.

---

## Yang-Chiribella-Hayashi (YCH) Series (2016-2018)

- **yang2016optimal**: Optimal compression for identically prepared qubit states (the qubit precursor to this project) [doi:10.1103/PhysRevLett.117.090502](https://doi.org/10.1103/PhysRevLett.117.090502)
- **yang2016efficient**: Efficient compression for mixed state ensembles
- **yang2018compression**: Compression for quantum population coding (qudits, leading order)
- **yang2018compressionfor**: Compression for qubit clocks

**Relevance:** Direct precursors. YCH established the qubit compression rate using Werner's cloning map. This project generalizes to qudits and identifies the $O(1)$ correction as free entropy.

---

## Werner and Keyl-Werner (1998-2001)

- **werner1998optimal**: Optimal cloning of pure states (Werner's cloning map) [doi:10.1103/PhysRevA.58.1827](https://doi.org/10.1103/PhysRevA.58.1827)
- **keyl1999optimal**: Optimal cloning, testing single clones
- **keyl2001rate**: Rate of optimal purification procedures
- **keyl2001estimating**: Estimating spectrum of density operator

**Relevance:** Werner's cloning map is the qubit special case of the [[concepts/generalized-cloning-map|Generalized Cloning Map]]. Keyl-Werner's spectrum estimation results underlie the compression scheme.

---

## Koashi-Imoto (2001-2002)

- **koashi2001compressibility**: Compressibility of quantum mixed-state signals [doi:10.1103/PhysRevLett.87.017902](https://doi.org/10.1103/PhysRevLett.87.017902)
- **koashi2001possible**: Operations that do not disturb partially known quantum states

**Relevance:** The [[concepts/koashi-imoto|Koashi-Imoto Structure Theorem]] is the key tool in the [[results/converse|Converse (State Compression)]].

---

## Representation Theory

- **parthasarathy1967**: PRV theorem (representations of complex semi-simple Lie groups)
- **kumar1988proof**: Proof of the PRV conjecture (multiplicity one) [doi:10.1007/BF01393689](https://doi.org/10.1007/BF01393689)
- **gelfand1950finite**: Gelfand-Tsetlin basis
- **fulton1991representation**: Standard reference for representation theory
- **macdonald1995symmetric**: Symmetric functions and Hall polynomials (Schur polynomials, Kostka numbers)

**Relevance:** The mathematical toolkit. PRV theorem defines the [[concepts/prv-component|PRV Component]], GT basis enables explicit computations.

---

## Davis-Kahan (1970)

- **davis1970rotation**: The rotation of eigenvectors by a perturbation [doi:10.1137/0707001](https://doi.org/10.1137/0707001)

**Relevance:** The [[results/lemmas/davis-kahan|Davis-Kahan Theorem (Lemma 6)]] is the workhorse of the [[results/lemmas/perturbation-lemma|Perturbation Lemma (Lemma 7)]].

---

## Quantum Information Foundations

- **schumacher1995quantum**: Quantum coding (Schumacher compression -- the von Neumann entropy analogue) [doi:10.1103/PhysRevA.51.2738](https://doi.org/10.1103/PhysRevA.51.2738)
- **jozsa1998universal**: Universal quantum information compression
- **hayashi2002simple**, **hayashi2002quantum**, **hayashi2010universal**: Quantum variable-length source coding

**Relevance:** The classical (von Neumann) compression theory that QMDL generalizes.

---

## Quantum Kolmogorov Complexity

- **rissanen1978modeling**: Classical MDL principle [doi:10.1016/0005-1098(78)90005-5](https://doi.org/10.1016/0005-1098(78)90005-5)
- **Berthiaume_2001**: Quantum Kolmogorov complexity
- **G_cs_2001**: Quantum algorithmic entropy
- **mueller2007**: Quantum Kolmogorov complexity and quantum Turing machines

**Relevance:** The project's QMDL can be viewed as a quantum analogue of Rissanen's minimum description length principle.

---

## Related Recent Work

- **yang2025compression**: Compression of quantum shallow-circuit states
- **li2025purity**: Optimal quantum purity amplification
- **vardhan2025**: Free mutual information and higher-point OTOCs (connects free entropy to quantum chaos)
