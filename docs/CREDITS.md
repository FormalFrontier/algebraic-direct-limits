# Contributors and provenance

Authors: Formal Frontier Agents. Original project contributions are distributed
under the complete [Apache-2.0 license](../LICENSE). This collective author credit
does not identify a legal copyright holder. The development and assembly used
AI-assisted agents; no human or source-author endorsement is asserted.

The mathematical Lean expressions in this library are original Formal Frontier
project contributions, not transcriptions of the mathematical references or
upstream mathlib code. Their contributions include:

| Modules and work | Project contributors |
| --- | --- |
| `VaryingScalar`, `CofinalSequence`, `MittagLeffler` | Anchor: original varying-scalar and tensor direct limits, cofinality, and Mittag-Leffler work |
| `SimpleRing`, `GradedStabilization` | Prism: original simple-ring filtered-colimit and graded work |
| `RingTheory.KrullDimension.FiniteCapture`, `RingTheory.KrullDimension.DirectLimit` and their examples | Keel: finite-subset capture, strict prime-chain contraction, subsemiring-preimage and directed-colimit dimension bounds, and finite-variable trace examples using Mathlib's Krull-dimension, prime-spectrum, set-restriction, polynomial, representative and characteristic-map APIs |
| `LocalizationPi`, `CofinalGroupCompletion` and their boundary clients | Other Formal Frontier agents: original formalizations |
| `MonoidalGroupCompletion` and its boundary client | Other Formal Frontier agents: formal Lean development informed by Prism's original monoidal research |
| `Topology.Restriction` and its clients | Ember: generalization of the same-topology restriction object and continuous-map construction in Continuous Group Cohomology, including Beacon's original development |
| Public imports, readiness clients, documentation, configuration and mathematical refinements | Anchor and other Formal Frontier agents: assembly and later project work |

Prism's monoidal research informed the later reusable Lean extraction; it is
credited as mathematical research and method input, not as a shipped import or
an independently distributed source artifact. The documentation adapter in
`scripts/generate_api.py` adapts Anchor's original Formal Frontier adapter from
the ideal-completion project under the same project Apache-2.0 authorization.
Anchor also authored the display inventory, supplementary API notes and associated
controls. These project adaptations are distinct from dependency code: the
generated reference reproduces this library's signatures and source docstrings,
not doc-gen4's implementation or website assets.

[mathlib4](https://github.com/leanprover-community/mathlib4) supplies separately
licensed formal foundations as a declared dependency, rather than the original
expression of the project modules above. Lean and doc-gen4 are likewise separately
maintained tools; their implementations and notices remain upstream, not vendored
here. The [Stacks Project lemma on Mittag-Leffler systems](https://stacks.math.columbia.edu/tag/0597)
is mathematical background, not a copied text, a source-coverage claim or an
endorsement. No book PDF, scan, figure or substantial source excerpt is shipped.

Same-topology restriction uses Jujian Zhang's Mathlib algebraic change-of-rings
functor and comparison isomorphisms, Sébastien Gouëzel and Yury Kudryashov's
continuous-linear restriction, and Richard Hill and Andrew Yang's topological
module category. Its categorical packaging builds on the existing scalar-
extension formalization in
[Continuous Group Cohomology](https://github.com/FormalFrontier/continuous-group-cohomology),
not a separately implemented scalar action. The regular-action continuity
criterion generalizes Mathlib's `continuous_algebraMap_iff_smul` in
`Topology.Algebra.Algebra`, by Kim Morrison, Antoine Chambert-Loir and
María Inés de Frutos-Fernández; its Algebra agreement uses `Algebra.smul_def`.

The project's Apache-2.0 authorization covers verified original contributions
reused across Formal Frontier repositories. Authentic third-party notices must be
preserved wherever third-party material is incorporated; neither this license
label nor collective authorship substitutes for review of concrete rights issues.
