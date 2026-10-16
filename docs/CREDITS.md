# Contributors and provenance

Authors: Formal Frontier Agents. Original project contributions are distributed
under the complete [Apache-2.0 license](../LICENSE). This collective author credit
does not identify a legal copyright holder. The development and assembly used
AI-assisted agents; no human or source-author endorsement is asserted.

The mathematical Lean expressions in this library are original Formal Frontier
project contributions, not transcriptions of the mathematical references or
upstream mathlib code. Their contributions include:

| Modules and work | Contributions |
| --- | --- |
| `VaryingScalar`, `CofinalSequence`, `MittagLeffler` | Original varying-scalar and tensor direct limits, cofinality, and Mittag-Leffler work |
| `SimpleRing`, `GradedStabilization` | Original simple-ring filtered-colimit and graded work |
| `RingTheory.KrullDimension.FiniteCapture`, `RingTheory.KrullDimension.DirectLimit` and their examples | Finite-subset capture, strict prime-chain contraction, subsemiring-preimage and directed-colimit dimension bounds, and finite-variable trace examples using Mathlib's Krull-dimension, prime-spectrum, set-restriction, polynomial, representative and characteristic-map APIs |
| `Order.DirectedSystem`, `RingTheory.DirectLimit` | Generalization of the original constant-integer identity-system law and its specialization to identity ring homomorphisms |
| `LocalizationPi`, `CofinalGroupCompletion` and their boundary clients | Original formalizations |
| `MonoidalGroupCompletion` and its boundary client | Formal Lean development informed by original Formal Frontier monoidal research |
| `Topology.Coinduced`, `Topology.TensorProduct`, `Topology.TensorHom`, `Topology.TensorUnit` and their examples | One-sided topological-module development following the original Formal Frontier Continuous Group Cohomology ideas and Mathlib's Richard Hill/Andrew Yang constructions |
| Arbitrary product coordinates, generalized tensor separation statements and infinite/projective examples | Original split-cover mathematics and Lean expressions applying the existing universal lift, stock basis coordinates and projective splitting |
| `Topology.Restriction` and its clients | Generalization of the same-topology restriction object and continuous-map construction in Continuous Group Cohomology, including the original topological development |
| `Topology.DiscreteScalarExtension` and its matrix-coefficient client | Generalization of the Continuous Group Cohomology scalar object, maps and unit, following the original topological development and reusing the one-sided tensor primitives |
| Public imports, examples, documentation, configuration and mathematical refinements | Assembly and mathematical refinements |

Original Formal Frontier monoidal research informs the reusable Lean development
as mathematical ideas and methods, not dependency code. The documentation adapter
in `scripts/generate_api.py` adapts the project's original ideal-completion
adapter under the same Apache-2.0 authorization. The documentation tooling and
supplementary API notes are also original project contributions. These adaptations
are distinct from dependency code: the generated reference reproduces this library's
signatures and source docstrings, not doc-gen4's implementation or website assets.

[mathlib4](https://github.com/leanprover-community/mathlib4) supplies separately
licensed formal foundations as a declared dependency, rather than the original
expression of the project modules above. Lean and doc-gen4 are likewise separately
maintained tools; their implementations and notices remain upstream, not vendored
here. The [Stacks Project lemma on Mittag-Leffler systems](https://stacks.math.columbia.edu/tag/0597)
is mathematical background, not a copied text, a source-coverage claim or an
endorsement. No book PDF, scan, figure or substantial source excerpt is shipped.

The constant-identity directed-system construction reuses Junyan Xu's
[`DirectedSystem` class and its law API](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/Order/DirectedInverseSystem.lean).
It generalizes the original constant-integer directed-colimit client, rather
than defining a new system class or colimit construction. The ring-homomorphism
instance returns this same function-law witness after identity-coercion conversion,
using Amelia Livingston and Jireh Loreaux's Mathlib `RingHom` API. The concrete
ring colimit and its universal lift reuse Junyan Xu's Mathlib construction; no
class law fields or colimit implementation are copied.

The tensor-coordinate and separation work reuses Mathlib's tensor-basis API by
Jakob von Raumer; basis and Finsupp APIs by Johannes Hölzl, Kim Morrison, Mario
Carneiro and Alexander Bentkamp; projective splitting by Kevin Buzzard and Antoine
Labelle; algebraic tensor maps and unitors by Kenny Lau and Mario Carneiro; and the
continuous-linear APIs by Jan-David Salchow, Sébastien Gouëzel, Jean Lo, Yury
Kudryashov, Frédéric Dupuis and Heather Macbeth. The infinite-basis finiteness
provider is due to Johan Commelin; dense-order topology to Johannes Hölzl, Mario
Carneiro and Yury Kudryashov; integer-action continuity to Johannes Hölzl, Mario
Carneiro and Patrick Massot; and the ideal API to Kenny Lau, Chris Hughes and Mario
Carneiro. Related general idempotent-ideal mathematics in Projective Modules
is mathematical input, not a dependency or copied generic
implementation. The fixed product-ring ideal uses canonical Mathlib module
structures and local specimen data.

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

The scalar-extension work follows the Continuous Group Cohomology formalization
by Formal Frontier Agents. Its earlier universe interface adapts Nailin Guan's
module-category universe-lift construction; that interface is not copied here.
The scalar layer reuses Mathlib's tensor and continuous-linear machinery
through the one-sided tensor primitives. Mathlib's topological-module category
is due to Richard Hill and Andrew Yang, its tensor APIs to Kenny Lau and Mario
Carneiro, its coefficient-linear tensor APIs to Kim Morrison, Johan Commelin and
Eric Wieser, and its change-of-rings API to Jujian Zhang.

The project's Apache-2.0 authorization covers verified original contributions
reused across Formal Frontier repositories. Authentic third-party notices must be
preserved wherever third-party material is incorporated; neither this license
label nor collective authorship substitutes for review of concrete rights issues.
