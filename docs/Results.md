# Mathematical results

These selected detailed descriptions include hypotheses, examples and limitations.
See the [library overview](../README.md#headline-results) for a selection,
[usage and reproduction](../README.md#using-the-library) for installation,
and the [mathematical guide](Guide.md) for explanations. Consult the linked
Lean modules for the exact statements and proofs.

## Headline results

- **Same-topology scalar restriction.**
  [`TopModuleCat.restrictScalarsObj`](../AlgebraicDirectLimits/Topology/Restriction.lean)
  retains the carrier, additive group and topology of a topological `S`-module
  along a continuous ring homomorphism `φ : R →+* S`. Both rings may be
  noncommutative and neither scalar topology must be discrete. The algebraic
  object is Mathlib's `ModuleCat.restrictScalars φ`; the restricted action is
  `r • x = φ r • x`. Continuous-linear maps support independent source and
  target carrier universes. Restriction is functorial, commutes with forgetting
  to modules and topological spaces, and has natural identity and composition
  comparisons. Separately, for arbitrary semirings with supplied topologies
  and continuous multiplication on `S`, continuity of `φ` is equivalent to joint
  continuity of its restricted regular action; evaluation at `1` gives necessity.
  The algebra-map formula agrees with Algebra scalar multiplication and recovers
  Mathlib's `continuous_algebraMap_iff_smul` for arbitrary scalar topologies.
  This is separate from continuous Hom statements for an already constructed
  extension object. No extension/restriction adjunction or finite-free continuous
  Hom equivalence is asserted. See the
  [coordinate-swap, matrix, semiring and Algebra clients](../AlgebraicDirectLimitsExamples/Restriction.lean).
- **One-sided tensor topology.**
  [`TopModuleCat.tensorLeftObj`](../AlgebraicDirectLimits/Topology/TensorProduct.lean)
  equips `C ⊗[R] M` with the coinduced topological-module topology for every
  `m ↦ c ⊗ₜ m`, over a commutative ring with a supplied topology. Only `M` is
  topological; neither factor has a finiteness hypothesis. Linear continuity out
  of the tensor is characterized by its continuous fixed-coefficient generators.
  The canonical `tensorMapCLM` realizes `TensorProduct.map` for an algebraic
  left-factor map and continuous right-factor map, with application, identity
  and composition laws. Finite-basis coordinates give a continuous linear
  equivalence with the finite product of `M`; the inverse reconstructs tensors
  by summing continuous basis generators. The scalar ring may be trivial and
  the basis index may be empty. Basis change remains a type contract, not a
  proved result.
  See the
  [integer-pair and boundary examples](../AlgebraicDirectLimitsExamples/TensorProduct.lean).
- **Arbitrary-basis and projective tensor Hausdorffness.**
  Over a commutative ring with a supplied topology, let `C` be algebraic and
  `M` a Hausdorff topological module with jointly continuous scalar action.
  [`TopModuleCat.t2Space_tensorLeftObj_of_basis`](../AlgebraicDirectLimits/Topology/TensorSeparation.lean)
  transfers Hausdorffness through continuous injective product coordinates for
  any supplied coefficient basis, without a finite-index hypothesis.
  [`TopModuleCat.t2Space_tensorLeftObj`](../AlgebraicDirectLimits/Topology/TensorSeparation.lean)
  gives the same preservation for any projective coefficient module. Its
  canonical free cover splits by projectivity; continuous tensor maps of the
  section and projection give a split embedding into a tensor with free
  coefficients. This uses splitness, not preservation of arbitrary injections
  or flatness. All carrier and basis-index universes are independent. No
  coefficient topology, right-module freeness or finiteness, scalar
  Hausdorffness, `TopologicalRing`, field or `Small` hypothesis is required.
  Empty bases and trivial scalar rings are allowed. The
  [separation examples](../AlgebraicDirectLimitsExamples/TensorSeparation.lean)
  use integer-pair coefficients, the nonfree right integer module `ZMod 3`,
  nonzero pure and mixed tensors, right doubling, and the noncompact Hausdorff
  integer right factor. Empty and trivial coefficient cases and zero
  coefficients with an indiscrete non-Hausdorff right factor illustrate why
  no Hausdorffness reflection is asserted. See also the
  [infinite-basis and nonfree projective models](../AlgebraicDirectLimitsExamples/ProjectiveTensorSeparation.lean).
  The compactness theorem is separate and assumes finitely generated coefficients
  and a compact right factor; projectivity alone does not supply finite generation.
- **Flat coefficients need not preserve tensor Hausdorffness.**
  [`TensorCircleExamples.not_t2Space_rationalCircleTensor`](../AlgebraicDirectLimitsExamples/TensorCircleClient.lean)
  proves that the integer tensor of `ℚ` with the usual real circle of period one
  is not Hausdorff for `TopModuleCat.tensorLeftObj`'s finest topological-module
  topology making all fixed-coefficient generators continuous. The coefficient
  module is flat and the circle is compact Hausdorff with jointly continuous
  integer action. The continuous generator at coefficient one vanishes on every
  rational angle but not at `[√2]`; Hausdorffness would force equality with zero
  everywhere by density. The detector remains purely algebraic, and no rational
  action on the circle is used. See the
  [counterexample and supporting results](#supporting-rational-circle-results).
- **Continuous tensor universal property.**
  [`TopModuleCat.tensorHomLinearEquiv`](../AlgebraicDirectLimits/Topology/TensorHom.lean)
  identifies continuous linear maps `C ⊗[R] M →L[R] N` with algebraic linear
  families `C →ₗ[R] (M →L[R] N)`. The coefficient module is purely algebraic;
  the ring is commutative with a supplied topology, and `M` and `N` have jointly
  continuous scalar actions. The explicit lift and curry constructions agree
  with Mathlib's algebraic tensor lift and commute with coefficient and
  continuous right-factor maps. The carrier universes are independent, and no
  topology on the Hom module or finiteness hypothesis is required. See the
  [integer-pair examples](../AlgebraicDirectLimitsExamples/TensorHom.lean), including
  a nonzero cross tensor annihilated by the dot pairing but detected by a second
  pairing.
  In the same module, an arbitrary supplied basis gives the continuous map
  [`tensorCoordinatesCLM`](../AlgebraicDirectLimits/Topology/TensorHom.lean)
  into the product of copies of the right factor. Its characteristic lemmas
  give pure-tensor and generator values, the algebraic Finsupp-coordinate
  support-forgetting formula, injectivity, and agreement with the forward
  finite-coordinate map when the basis index is finite. Injectivity follows
  from the algebraic Finsupp-coordinate equivalence, not an inverse on the
  whole infinite product; the coordinate map needs no separation hypothesis.
  Product coordinates detect equality for any supplied coefficient basis.
  The [coordinate laws](../AlgebraicDirectLimits/Topology/TensorHom.lean) do not
  give an infinite-product equivalence or surjectivity: a product tuple need
  not have finite support. The finite LE/CLE and their finite-sum inverses
  remain finite-only. The
  [additional models](../AlgebraicDirectLimitsExamples/ProjectiveTensorSeparation.lean)
  use non-finitely-generated coefficients `ℕ →₀ ℤ` with the usual nondiscrete
  real right module, and the nonfree projective ideal generated by `(1, 0)`
  over `ℤ × ℤ`. Their declarations include model properties, pure and mixed
  coordinate calculations, explicit open-set separation and applications of
  the preservation statements. Carrier and basis-index universes are independent.
- **Continuous scalar tensor unit.**
  [`TopModuleCat.tensorUnitContinuousLinearEquiv`](../AlgebraicDirectLimits/Topology/TensorUnit.lean)
  equips Mathlib's `TensorProduct.lid R M` with the one-sided tensor topology:
  `r ⊗ₜ m` maps to `r • m`, and its inverse is the continuous generator
  `m ↦ 1 ⊗ₜ m`. It is natural in continuous right-factor maps, over any
  commutative ring with a supplied topology and jointly continuous action on
  `M`, without continuity of ring multiplication or a finite basis. See the
  [integer-pair doubling examples](../AlgebraicDirectLimitsExamples/TensorUnit.lean).
- **Associativity for the one-sided tensor topology.**
  [`TopModuleCat.tensorAssocContinuousLinearEquiv`](../AlgebraicDirectLimits/Topology/TensorAssociativity.lean)
  equips Mathlib's algebraic associator `(C ⊗[R] D) ⊗[R] M ≃ₗ[R] C ⊗[R] (D ⊗[R] M)`
  with continuous forward and inverse maps for the supplied one-sided tensor
  topologies. Only `M` is topological; the commutative ring has a supplied
  topology and both coefficient modules are algebraic. Pure-tensor formulas,
  threefold extensionality, inverse identities and naturality in all three
  factors require no finiteness, freeness or separation hypothesis. See the
  [mixed integer-pair, nonfree torsion and empty-coefficient examples](../AlgebraicDirectLimitsExamples/TensorAssociativity.lean).
- **Continuous lift and curry compatibility with reassociation.**
  For algebraic `R`-modules `C,D` and topological `R`-modules `M,N`,
  [`TopModuleCat.tensorLiftCLM_lift_eq_comp_tensorAssoc`](../AlgebraicDirectLimits/Topology/TensorAssociativity.lean)
  says that the flat continuous lift of every family
  `b : C →ₗ[R] D →ₗ[R] (M →L[R] N)` equals its iterated lift composed with
  the canonical associator. For every outgoing continuous linear map on
  `C ⊗[R] (D ⊗[R] M)`,
  [`TopModuleCat.tensorCurry_comp_tensorAssoc`](../AlgebraicDirectLimits/Topology/TensorAssociativity.lean)
  identifies the whole curried family after reassociation with the algebraic
  lift of its twice-curried family. The scalar ring is commutative with a
  supplied topology; right and target scalar actions are jointly continuous.
  The five carrier universes are independent, with no coefficient or Hom
  topology, finiteness, freeness, discreteness or separation hypothesis.
  The [clients](../AlgebraicDirectLimitsExamples/TensorAssociativity.lean)
  compare the continuous lifts with algebraic coordinate detectors on arbitrary
  tensors, vary both right coordinates, distinguish nonzero functionals and
  lifts, and retain boundary controls for infinite integer coefficients with
  usual real factors and for a nonfree first-axis ideal over `ℤ × ℤ`.
- **Compactness with finitely generated coefficients.**
  [`TopModuleCat.compactSpace_tensorLeftObj`](../AlgebraicDirectLimits/Topology/TensorCompactness.lean)
  gives compactness of the one-sided tensor when its algebraic coefficient
  module is finitely generated and its topological right factor is compact.
  The commutative scalar ring has a supplied topology; neither a topology nor
  freeness is required of the coefficient module, and all three carrier
  universes are independent. A finite spanning family gives a continuous
  surjection from a finite power of the right factor. This includes finite-free
  coefficients and the
  [torsion example](../AlgebraicDirectLimitsExamples/TensorCompactness.lean), which
  uses `ZMod 3` over the integers, with a nonfree coefficient module and a
  nonzero pure tensor detected by multiplication.

  Finite generation cannot in general be omitted, even for free/projective
  coefficients and a nontrivial compact Hausdorff right factor. Over
  `R = ZMod 2`, the algebraic module `C = ℕ →₀ R` is countably free and
  projective but not finitely generated, while the discrete right self-module
  `M = R`, with its multiplication action, is nontrivial, compact and Hausdorff.
  Nevertheless,
  [`TensorNoncompactness.not_compactSpace_tensor`](../AlgebraicDirectLimitsExamples/TensorNoncompactness.lean)
  shows that their one-sided tensor is not compact. The right unitor gives a
  homeomorphism with an infinite discrete comparison module `D` retaining
  `C`'s algebraic module and action; its topology is not an input on `C`.
  If the tensor were compact, `D` would be compact and discrete, hence finite,
  contradicting the injection from `ℕ` given by the images of the basis tensors.
- **Varying scalars and tensor products.**
  [`DirectLimit.VaryingScalar.tensorProductEquiv`](../AlgebraicDirectLimits/VaryingScalar.lean#L429)
  identifies the tensor product of two module limits over a *varying*
  commutative-semiring limit with the limit of their stagewise tensor products.
  It uses compatible semilinear module systems over a nonempty directed preorder,
  with four independent universes and no injectivity assumption on transitions.
  See the [module](../AlgebraicDirectLimits/VaryingScalar.lean) and
  [representative client](../tests/ReadinessClient.lean#L54).
- **Coinduced topological modules.**
  [`TopModuleCat.continuous_coinduced_iff`](../AlgebraicDirectLimits/Topology/Coinduced.lean)
  characterizes continuity of a linear map out of Mathlib's existing coinduced
  topological module by continuity on every generator. It needs only a ring
  with a supplied topology, allows an empty index type and an independently
  leveled target, and does not assert a nonlinear final-topology property.
  The [examples](../AlgebraicDirectLimitsExamples/Coinduced.lean) use the two integer
  axes in `ℤ × ℤ` and the nonzero functional `(x, y) ↦ x + 2 * y`; addition on
  a product is also treated over a possibly noncommutative ring.
- **Sequentializing cofinality.**
  [`IsCofinal.exists_monotone_nat`](../AlgebraicDirectLimits/CofinalSequence.lean#L33)
  and [`exists_final_functor_nat`](../AlgebraicDirectLimits/CofinalSequence.lean#L55)
  produce a monotone cofinal sequence and a final functor from `ℕ` when a
  *nonempty directed preorder has a countable cofinal subset*; the entire index
  type need not be countable. See the [module](../AlgebraicDirectLimits/CofinalSequence.lean)
  and [client](../tests/ReadinessClient.lean#L106).
- **Mittag--Leffler inverse systems.**
  [`IsMittagLeffler.nonempty_sections_of_countable_cofinal`](../AlgebraicDirectLimits/MittagLeffler.lean#L66)
  gives a compatible section for a pointwise nonempty, Type-valued
  Mittag--Leffler inverse system over a nonempty directed preorder with a
  countable cofinal subset. Under the same index and Mittag--Leffler conditions,
  [`surjective_evalSectionToEventualRange`](../AlgebraicDirectLimits/MittagLeffler.lean#L97)
  lifts each element of an eventual range to a section; this second theorem does
  not separately assume pointwise nonemptiness. See the
  [module](../AlgebraicDirectLimits/MittagLeffler.lean) and
  [client](../tests/ReadinessClient.lean#L142).
- **Filtered colimits of simple rings.**
  [`RingCat.FilteredColimits.colimit_isSimpleRing`](../AlgebraicDirectLimits/SimpleRing.lean#L47)
  proves that a small filtered colimit of simple rings in the possibly
  noncommutative `RingCat` is simple. Stage-map injectivity follows from
  simplicity; it is not a diagram hypothesis. See the
  [module](../AlgebraicDirectLimits/SimpleRing.lean) and
  [client](../tests/ReadinessClient.lean#L162).
- **Prime spectra of filtered colimits.** For a small filtered category and
  any colimit cocone of commutative rings,
  [`PrimeSpectrum.colimitCone_isLimit`](../AlgebraicDirectLimits/PrimeSpectrumFilteredColimits.lean)
  identifies its spectrum cone as a limit **in topological spaces**. The
  [chosen-limit homeomorphism and projection law](../AlgebraicDirectLimits/PrimeSpectrumFilteredColimits.lean)
  identify each coordinate with contraction along its cocone map. No
  injectivity, nonzero-ring, nonempty-spectrum or separation hypothesis is
  required. See the [constant, quotient and empty-spectrum examples](../AlgebraicDirectLimitsExamples/PrimeSpectrumFilteredColimits.lean).
- **Krull dimension under finite-subset capture.** For a family of homomorphisms
  `φ i : A i →+* B` between commutative semirings, if every finite subset of `B`
  lies in the range of one `φ i`, then
  [`ringKrullDim_le_iSup_of_finite_subset_range`](../AlgebraicDirectLimits/RingTheory/KrullDimension/FiniteCapture.lean)
  bounds `ringKrullDim B` by `⨆ i, ringKrullDim (A i)`. The family need not be
  directed and the maps need not be injective; dimensions include `⊥` and `⊤`.
  The same [module](../AlgebraicDirectLimits/RingTheory/KrullDimension/FiniteCapture.lean)
  gives the bound by subsemirings generated by finite subsets. For any
  subsemiring `C` of `B`,
  [`ringKrullDim_subsemiring_le_iSup_comap_of_finite_subset_range`](../AlgebraicDirectLimits/RingTheory/KrullDimension/FiniteCapture.lean)
  bounds `ringKrullDim C` by `⨆ i, ringKrullDim (C.comap (φ i))`, using
  the same finite-subset hypothesis on `B`. See the
  [surjective, polynomial and empty-family examples](../AlgebraicDirectLimitsExamples/RingTheory/KrullDimension/FiniteCapture.lean),
  [proper even-variable subsemiring traces](../AlgebraicDirectLimitsExamples/RingTheory/KrullDimension/FiniteCaptureTrace.lean)
  and the [aggregate-import client](../tests/FiniteCaptureClient.lean).
  The [guide](Guide.md#krull-dimension-under-finite-subset-capture)
  distinguishes one common stage for each finite subset from pointwise capture.
- **Krull dimension of directed colimits.** For commutative semirings over a
  nonempty directed preorder, with compatible ring-homomorphism transitions,
  [`ringKrullDim_directLimit_le_iSup`](../AlgebraicDirectLimits/RingTheory/KrullDimension/DirectLimit.lean)
  bounds the dimension of `DirectLimit G f` by `⨆ i, ringKrullDim (G i)`.
  The index and stage universes are independent. No injectivity, Noetherianity,
  domain, nontriviality or finite-dimension hypothesis is needed; dimensions
  retain `⊥` and `⊤`. The proof applies finite-subset capture to the canonical
  stage maps. See the [constant integer and noninjective quotient models](../AlgebraicDirectLimitsExamples/RingTheory/KrullDimension/DirectLimit.lean).
- **Krull dimension of directed subsemiring unions.** For a nonempty family
  `s : ι → Subsemiring R` in a commutative semiring, directed under inclusion,
  [`Subsemiring.ringKrullDim_iSup_le`](../AlgebraicDirectLimits/RingTheory/KrullDimension/DirectedUnion.lean)
  bounds `ringKrullDim (⨆ i, s i : Subsemiring R)` by `⨆ i, ringKrullDim (s i)`.
  The index needs no order, and its universe is independent of the ambient
  semiring's. No Noetherianity, domain, nontriviality or finite-dimension
  hypothesis is needed; dimension values include `⊥` and `⊤`. The proof uses
  canonical inclusions and finite-subset capture. See the
  [proper integer-to-rational family and empty-index boundary](../AlgebraicDirectLimitsExamples/RingTheory/KrullDimension/DirectedUnion.lean).
  This is only an upper bound: the proper two-stage family indexed by `Bool`
  in `ℚ` has stage-dimension supremum one and union dimension zero.
- **Localization of a countable product.**
  [`Localization.awayPiComparison`](../AlgebraicDirectLimits/LocalizationPi.lean#L26)
  compares localization of `ℕ → R` at a constant `r` with the countable product
  of localizations of `R` away from `r`.
  [`awayPiComparison_not_surjective`](../AlgebraicDirectLimits/LocalizationPi.lean#L50)
  shows non-surjectivity if `R` is a commutative domain and `r` is nonzero and
  not a unit; no finite-product claim follows. See the
  [module](../AlgebraicDirectLimits/LocalizationPi.lean) and
  [client](../tests/ReadinessClient.lean#L172).
- **Cofinal submonoids and group completion.** If an additive submonoid `L`
  of an arbitrary additive commutative monoid has top saturation, the canonical
  completion map [localizes at `L`](../AlgebraicDirectLimits/CofinalGroupCompletion.lean#L31).
  This supplies [denominators](../AlgebraicDirectLimits/CofinalGroupCompletion.lean#L57),
  [a stabilization test for equal images](../AlgebraicDirectLimits/CofinalGroupCompletion.lean#L64)
  and [injectivity on completion of the inclusion](../AlgebraicDirectLimits/CofinalGroupCompletion.lean#L71).
  No cancellation is assumed. See the
  [module](../AlgebraicDirectLimits/CofinalGroupCompletion.lean) and
  [client](../tests/CofinalGroupCompletionClient.lean#L41).
- **Monoidal object classes.** For a strong monoidal functor, the
  [image submonoid](../AlgebraicDirectLimits/MonoidalGroupCompletion.lean#L71)
  consists of its *actual* image on additive skeleta. For braided target `D`,
  [`saturation_eq_top_iff`](../AlgebraicDirectLimits/MonoidalGroupCompletion.lean#L87)
  identifies its cofinality with every target object acquiring a complement
  isomorphic to a source-image object. Under this object-cofinality condition,
  there are object denominators and stabilization. If, additionally, the source
  is braided and the functor is fully faithful,
  [`completionMap_injective`](../AlgebraicDirectLimits/MonoidalGroupCompletion.lean#L230)
  makes the induced completion map injective; the
  [additive equivalence](../AlgebraicDirectLimits/MonoidalGroupCompletion.lean#L238)
  is to its *range*, not necessarily the whole target completion. Neither
  cancellation nor essential surjectivity is needed. See the
  [module](../AlgebraicDirectLimits/MonoidalGroupCompletion.lean) and
  [client](../tests/MonoidalGroupCompletionClient.lean#L169).
- **Graded stabilization.** For `d : M →+ A` and `u : M`,
  [normalization](../AlgebraicDirectLimits/GradedStabilization.lean#L112)
  sends the limit of fibers `d m = n • d u` to the kernel of the induced
  group-completion degree map. Top saturation of the multiples of `u` gives
  [injectivity](../AlgebraicDirectLimits/GradedStabilization.lean#L158);
  **cancellation in the degree target `A` only** additionally gives
  [surjectivity](../AlgebraicDirectLimits/GradedStabilization.lean#L195)
  and [`normalizationEquiv`](../AlgebraicDirectLimits/GradedStabilization.lean#L210),
  an equivalence **of types**, not an additive equivalence. Source monoid
  cancellation and injective transitions are not required. See the
  [module](../AlgebraicDirectLimits/GradedStabilization.lean) and
  [boundary client](../tests/GradedStabilizationClient.lean#L125).

The library does not supply full categorical tensor coherence or a pentagon
construction, completed tensor products, infinite-product surjectivity, or a
complete theory of limits. Hausdorff preservation for arbitrary flat coefficients
is ruled out by the rational-circle counterexample. Basis change remains a type
contract.

## Tensor–Hom naturality

In [`Topology.TensorHom`](../AlgebraicDirectLimits/Topology/TensorHom.lean),
`tensorLiftCLM_comp_tensorMapCLM` states, for arbitrary
`b : C →ₗ[R] (M →L[R] N)`, `a : D →ₗ[R] C` and `g : P →L[R] M`,

```text
tensorLiftCLM R ((ContinuousLinearMap.lcomp N g).comp (b.comp a)) =
  (tensorLiftCLM R b).comp (tensorMapCLM R a g).
```

This is equality of entire maps `tensorLeftObj R D P →L[R] N`, with six
independent scalar/coefficient/module carrier universes. Its algebraic-forgetting
counterpart is Mathlib's `TensorProduct.lift_comp_map`, applied to the linearized
continuous family, `a` and `g.toLinearMap`, with the opposite written orientation.
The existing `tensorLiftCLM_toLinearMap`, `tensorMapCLM_toLinearMap` and
`ContinuousLinearMap.toLinearMap_comp` supply the representation comparisons.
The statement concerns the continuous representation of that algebraic law for
the canonical one-sided topology, not a new algebraic theorem or a generalization
of a normed tensor topology.

`tensorCurry_comp` states, for arbitrary `f : tensorLeftObj R C M →L[R] N`
and `h : N →L[R] P`,

```text
tensorCurry R (h.comp f) =
  ((ContinuousLinearMap.llcomp R M N P).flip h).comp (tensorCurry R f).
```

This is equality of entire families `C →ₗ[R] (M →L[R] P)`, with five independent
carrier universes and no extra coefficient object. Both statements use a
commutative ring with a supplied topology, algebraic coefficient objects and
full topological modules with jointly continuous scalar actions. Neither adds
coefficient or Hom topologies, finite-generation, free, field, projective, basis,
Hausdorffness, discrete-scalar or topological-ring assumptions. The existing
lift-postcomposition and curry-input-precomposition theorems remain unchanged.

The [naturality model module](../AlgebraicDirectLimitsExamples/TensorHomNaturality.lean)
contains ten input declarations: regular integer coefficients, two integer-axis
inclusions, integer target doubling, the ordinary real product module, basis-vector
inclusions, real doubling, coordinate readouts, product-ring doubling and the
ideal inclusion paired with the continuous regular identity. Six whole-map
statements keep their families or outgoing maps arbitrary; three additional
statements give variable mixed-tensor formulas.
The integer model restricts different coefficient axes while doubling the right
factor and target. The infinite model uses `ℕ →₀ ℤ`, the usual nondiscrete reals
and ordinary Pi projections, not an infinite-product tensor equivalence. The
ideal model uses the nonfree first-axis ideal over the componentwise ring
`ℤ × ℤ`, its regular-to-ideal retraction and regular-module doubling. Three tuples
combine existing proof values detecting nonzero and distinct tensors, nonfinite
coefficients, nondiscrete right topology and nonfree nontrivial coefficients.
The model formulas express coefficient restrictions and target postcomposition
on arbitrary mixed tensors.

The module follows the existing integer-dot and arbitrary-coordinate/ideal examples
by Formal Frontier Agents, including Beacon's continuous-group-cohomology approach
and Lantern's coordinate and split-cover mathematics. Mathlib's tensor naturality
and universal-property APIs are by Kenny Lau and Mario Carneiro; the imported
modules preserve the detailed credits for topological modules, continuous linear
maps, Finsupp, basis, product and ideal constructions. No original source-text
coverage is asserted.

## Supporting rational-circle results

The [model](../AlgebraicDirectLimitsExamples/TensorCircleModel.lean) fixes
`TensorCircleExamples.rationalCoefficients : ModuleCat ℤ` to be `ℚ`, flat by
Mathlib's stock localization theorem `IsLocalization.flat`. Its `circleModule`
is the usual quotient `AddCircle (1 : ℝ)`, compact and Hausdorff with jointly
continuous integer scalar multiplication. The canonical `rationalCircleTensor`
is `TopModuleCat.tensorLeftObj ℤ rationalCoefficients circleModule`: the finest
integer-topological-module topology making every fixed-coefficient generator
continuous. In particular, `circleTensorGenerator` is the continuous integer-linear
map `m ↦ 1 ⊗ₜ[ℤ] m`. No coefficient topology or global tensor topology instance
is introduced.

The [algebraic detector](../AlgebraicDirectLimits/Topology/TensorCircle/Detector.lean)
has target `AddCircle.RationalQuotient = ℝ ⧸ Submodule.span ℚ {(1 : ℝ)}`.
The detector is the tensor lift of an integer-balanced bilinear map and sends
`q ⊗ [x]` to the class of `(q : ℝ) * x`.
The [client's `circleTensorDetector_tmul`](../AlgebraicDirectLimitsExamples/TensorCircleClient.lean)
gives the pure-tensor law for every `q : ℚ` and `m : circleModule`; its
`circleTensorDetector_tmul_coe` gives the real-representative formula, and
`circleTensorDetector_comp_generator` identifies the linear composite at
coefficient one with `AddCircle.toRationalQuotient`.
The same client proves that the detector of `irrationalGenerator` is the nonzero
class of `Real.sqrt 2`, and that the actual tensor `1 ⊗ [Real.sqrt 2]` is nonzero,
in `circleTensorDetector_irrationalGenerator_ne_zero` and `irrationalGenerator_ne_zero`.

The [rational-angle laws](../AlgebraicDirectLimits/Topology/TensorCircle/RationalAngles.lean)
prove `AddCircle.denseRange_rationalAngle` in the usual circle topology. Each
rational angle has its positive integer denominator as an annihilator, and
`TensorProduct.tmul_rationalAngle_eq_zero` gives
`c ⊗ₜ[ℤ] AddCircle.rationalAngle q = 0` for **all** `c q : ℚ`.
The balancing argument divides only the rational coefficient, not the circle point.
`TopModuleCat.tensorGenerator_rationalAngle` gives the corresponding law for
every fixed-coefficient continuous generator. The client's `rationalAngle_boundaries`
also exhibits the nonzero half-angle killed by `circleTensorGenerator`.

The client's `TensorCircleExamples.rationalCircle_properties` combines twelve
supporting properties of these fixed modules and maps without additional hypotheses.
The same client proves `TensorCircleExamples.not_t2Space_rationalCircleTensor`:
this tensor is not Hausdorff. If it were Hausdorff, Mathlib's
`Continuous.ext_on` would make the generator at one equal to the zero map, since both
are continuous and agree on the dense range of `AddCircle.rationalAngle`.
Evaluation at `[√2]` contradicts `irrationalGenerator_ne_zero`. The model and its
twelve supporting properties have no extra hypotheses. The detector and its
target remain purely algebraic, with no topology or continuity asserted;
rational scalars act on the coefficients and quotient, not on the circle.

Return to the [library overview](../README.md).
