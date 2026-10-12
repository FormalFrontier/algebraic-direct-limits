# Mathematical results

The full descriptions below include hypotheses, examples and limitations.
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
- **Varying scalars and tensor products.**
  [`DirectLimit.VaryingScalar.tensorProductEquiv`](../AlgebraicDirectLimits/VaryingScalar.lean#L429)
  identifies the tensor product of two module limits over a *varying*
  commutative-semiring limit with the limit of their stagewise tensor products.
  It uses compatible semilinear module systems over a nonempty directed preorder,
  with four independent universes and no injectivity assumption on transitions.
  See the [module](../AlgebraicDirectLimits/VaryingScalar.lean) and
  [representative client](../tests/ReadinessClient.lean#L48).
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
  and [client](../tests/ReadinessClient.lean#L100).
- **Mittag--Leffler inverse systems.**
  [`IsMittagLeffler.nonempty_sections_of_countable_cofinal`](../AlgebraicDirectLimits/MittagLeffler.lean#L66)
  gives a compatible section for a pointwise nonempty, Type-valued
  Mittag--Leffler inverse system over a nonempty directed preorder with a
  countable cofinal subset. Under the same index and Mittag--Leffler conditions,
  [`surjective_evalSectionToEventualRange`](../AlgebraicDirectLimits/MittagLeffler.lean#L97)
  lifts each element of an eventual range to a section; this second theorem does
  not separately assume pointwise nonemptiness. See the
  [module](../AlgebraicDirectLimits/MittagLeffler.lean) and
  [client](../tests/ReadinessClient.lean#L136).
- **Filtered colimits of simple rings.**
  [`RingCat.FilteredColimits.colimit_isSimpleRing`](../AlgebraicDirectLimits/SimpleRing.lean#L47)
  proves that a small filtered colimit of simple rings in the possibly
  noncommutative `RingCat` is simple. Stage-map injectivity follows from
  simplicity; it is not a diagram hypothesis. See the
  [module](../AlgebraicDirectLimits/SimpleRing.lean) and
  [client](../tests/ReadinessClient.lean#L156).
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
  [client](../tests/ReadinessClient.lean#L166).
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
  sends the native limit of fibers `d m = n • d u` to the kernel of the induced
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
construction, preservation for arbitrary flat coefficients, completed tensor
products, infinite-product surjectivity, or a complete theory of limits.
Basis change remains a type contract.

Return to the [library overview](../README.md).
