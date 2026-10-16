# Algebraic Direct Limits

Authors: Formal Frontier Agents. License: [Apache-2.0](LICENSE).

This library works with mathlib's directed limits, localizations,
Grothendieck group completions and categorical colimits. Import the
[public aggregate](AlgebraicDirectLimits.lean) with `import AlgebraicDirectLimits`
for the core APIs, or import the linked mathematical modules individually.
The rational-circle modules listed below are separate imports.

## Headline results

- **Module topology on finite-dimensional strong duals.**
  [`IsModuleTopology.strongDual`](AlgebraicDirectLimits/Topology/StrongDual.lean)
  gives the module topology on the continuous dual of any finite-dimensional
  topological vector space already carrying the module topology, over a normed
  field. The field need not be complete or nontrivially normed, and the original
  space needs no norm. The dual retains its existing topology of uniform
  convergence on bounded sets, which is the operator-norm topology in the normed
  setting. This is an explicit theorem, not a global instance. The
  [examples](AlgebraicDirectLimitsExamples/StrongDual.lean) apply it to linear
  forms on the dual of the rational plane, include dimension zero, and record
  agreement with Mathlib's complete-field conclusion on the same topology.

- **Additive tensoring with fixed algebraic coefficients.**
  [`TopModuleCat.tensorLeftFunctor`](AlgebraicDirectLimits/Topology/TensorFunctor.lean)
  sends `M : TopModuleCat.{uM} R` to `tensorLeftObj R C M` for a fixed
  `C : ModuleCat.{uC} R`, retaining the canonical tensor action and one-sided
  topology. Morphisms act by tensoring the coefficient identity with the given
  continuous linear map. The ring is commutative with a supplied topology, and
  the input has a jointly continuous scalar action. Scalar and carrier universes
  are independent, with target `TopModuleCat.{max uC uM} R`; no coefficient
  topology, finiteness, freeness, separation or continuity of ring multiplication
  is required. The [characteristic API](AlgebraicDirectLimits/Topology/TensorFunctor.lean)
  exposes the object, continuous map, underlying algebraic map and pure-tensor
  formula. The stock `Functor.Additive` instance supplies `Functor.map_add` and
  `Functor.map_zero`. The [integer-pair examples](AlgebraicDirectLimitsExamples/TensorFunctor.lean)
  identify the doubled nonzero tensor and evaluate doubling plus identity.

- **Tensor functoriality in both variables.**
  [`TopModuleCat.tensorBifunctor`](AlgebraicDirectLimits/Topology/TensorBifunctor.lean)
  sends each algebraic coefficient module to its existing right-variable tensor
  functor. Its coefficient components are the existing coefficient-tensor maps;
  the standard `Functor.uncurry` acts by `tensorMapBilinear`, and `Functor.flip`
  recovers the coefficient functor. The commutative ring has a supplied topology,
  and right modules have jointly continuous actions. Scalar and carrier universes
  are independent, with target carrier universe `max uC uM`; no coefficient
  topology, finiteness, freeness, separation or continuity of ring multiplication
  is required. The [integer example](AlgebraicDirectLimitsExamples/TensorBifunctor.lean)
  tensors doubling with tripling and detects a nonzero image as six.

- **Bundled continuous tensor maps.**
  [`TopModuleCat.tensorMapBilinear`](AlgebraicDirectLimits/Topology/TensorProduct.lean)
  is bilinear in an algebraic coefficient map and a continuous linear right-factor
  map, with values in continuous linear maps between the canonical one-sided
  tensors. The ring is commutative with a supplied topology; the right-factor
  topological modules supply continuous addition and jointly continuous scalar
  actions. All carrier universes are independent. Forgetting continuity of the
  whole bundle gives Mathlib's `TensorProduct.mapBilinear` at the identity ring
  homomorphism. No coefficient or Hom topology, continuity of ring operations,
  finiteness or separation hypothesis is required. The
  [integer examples](AlgebraicDirectLimitsExamples/TensorProduct/Map.lean) detect
  the unit tensor as one and the images under two independently scaled maps as six.

- **Additive scalar restriction preserves kernels and cokernels.**
  For possibly noncommutative rings `R` and `S` with supplied topologies and a
  continuous unital homomorphism `φ : R →+* S`, the same-topology functor
  `TopModuleCat.restrictScalars φ hφ` is
  [additive and preserves each kernel](AlgebraicDirectLimits/Topology/RestrictionKernels.lean)
  and [each cokernel](AlgebraicDirectLimits/Topology/RestrictionCokernels.lean).
  The scalar and module universes are independent; the topological modules have
  jointly continuous scalar actions. Use Mathlib's `kernelComparison`,
  `cokernelComparison`, `PreservesKernel.iso` and `PreservesCokernel.iso` for the
  canonical comparisons. `TopModuleCat.restrictScalars_coker_existsUnique`
  factors continuous `R`-linear arrows killing the restricted map into arbitrary
  topological `R`-modules, without an `S`-action on the target.
  Cokernels use the algebraic range, not its
  closure; no topological-ring, separation, closed-range, injectivity,
  finiteness, freeness or flatness hypothesis is needed. The discrete
  `ℤ → ZMod 4` doubling models exhibit a
  [nonzero kernel element over `2`](AlgebraicDirectLimitsExamples/RestrictionKernels.lean)
  and a [nonzero quotient class of `1`](AlgebraicDirectLimitsExamples/RestrictionCokernels.lean),
  with a nonzero parity descendant into `ℤ × ZMod 2`.

- **Coefficient tensor–continuous Hom adjunction.**
  Let `R` be a commutative ring equipped with a topology and `M` a topological
  `R`-module with jointly continuous scalar action. In a common carrier universe,
  independent of the scalar universe, coefficient tensor is left adjoint to the
  existing algebraic continuous-Hom functor. Its characteristic Hom equivalence
  is the natural coefficient-family currying equivalence. It therefore preserves
  existing colimits of arbitrary diagram size. Neither coefficients nor the Hom
  module are given a topology. See the
  [module](AlgebraicDirectLimits/Topology/CoefficientTensor.lean),
  [naturality guide](docs/coefficient-tensor-hom-naturality.md),
  [integer evaluations](AlgebraicDirectLimitsExamples/CoefficientTensor.lean), and
  [endomorphism counit and binary coproduct](AlgebraicDirectLimitsExamples/CoefficientTensorAdjunction.lean).

- **Continuous tensor quotients.**
  [`TopModuleCat.tensorQuotient`](AlgebraicDirectLimits/Topology/TensorProduct/Quotient.lean)
  gives a continuous linear equivalence
  `C ⊗[R] (M ⧸ P) ≃L[R] (C ⊗[R] M) ⧸ K`, where
  `K = LinearMap.range (TensorProduct.map LinearMap.id P.subtype)`.
  The target is the canonical cokernel of the continuous submodule tensor map,
  not a quotient by the closure of its range. The ring is commutative with a
  supplied topology, `C` is purely algebraic, `M` is a topological module with jointly
  continuous scalar action and `P` is any submodule. Carrier universes are independent; no
  coefficient topology, continuity of ring multiplication, closedness,
  separation, finiteness, freeness, flatness or injectivity of the submodule tensor map
  is required. The underlying equivalence is
  `TensorProduct.tensorQuotientEquiv C P`. Characteristic formulas describe the
  forward and inverse maps on arbitrary and pure tensors; the existing
  continuous-linear-equivalence API supplies both round trips. The
  [examples](AlgebraicDirectLimitsExamples/CoefficientTensorQuotient.lean) use
  `(ZMod 2 × ZMod 2) × (ℕ →₀ ℤ)` and right submodules `2ℤ × B` of `ℤ × ℝ`,
  including the rational span of `1` restricted to `ℤ`, which is not closed.
  They give block maps, distinct-index detectors and doubling controls.
- **Discrete right-factor tensors.**
  [`TensorProduct.continuousSMul_bot_of_discrete_right`](AlgebraicDirectLimits/Topology/TensorDiscrete.lean)
  gives joint scalar continuity on the algebraic tensor with bottom topology, and
  [`TopModuleCat.discreteTopology_tensorLeftObj`](AlgebraicDirectLimits/Topology/TensorDiscrete.lean)
  gives discreteness of the canonical one-sided tensor. The ring is commutative
  with a supplied topology, the coefficients are purely algebraic, and the right
  topological module has a jointly continuous action and discrete topology.
  Scalar, coefficient and right-factor universes are independent; no discrete
  scalar topology, coefficient topology, finiteness, freeness or projectivity is
  required. The [examples](AlgebraicDirectLimitsExamples/DiscreteTensor.lean) give
  non-finitely-generated mod-two coefficients and a discrete integer module over
  the nondiscrete ring `ℤ × ℝ`, with nonzero and distinct tensor detectors.
  The unitors used for detection are algebraic; their continuity is not asserted.
- **Continuous tensor universal property.**
  [`TopModuleCat.tensorHomLinearEquiv`](AlgebraicDirectLimits/Topology/TensorHom.lean)
  identifies continuous linear maps `C ⊗[R] M →L[R] N` with algebraic linear
  families `C →ₗ[R] (M →L[R] N)`. The coefficient module is purely algebraic;
  the ring is commutative with a supplied topology, and `M` and `N` have jointly
  continuous scalar actions. The explicit lift and curry constructions agree
  with Mathlib's algebraic tensor lift and commute with coefficient and
  continuous right-factor maps. The carrier universes are independent, and no
  topology on the Hom module or finiteness hypothesis is required. See the
  [integer-pair examples](AlgebraicDirectLimitsExamples/TensorHom.lean), including
  a nonzero cross tensor annihilated by the dot pairing but detected by a second
  pairing.
- **Continuous dual tensor contraction.**
  [`TopModuleCat.dualTensorHom`](AlgebraicDirectLimits/Topology/DualTensorHom.lean)
  sends `φ ⊗ₜ v` to `w ↦ φ w • v`, from the existing one-sided tensor with
  algebraic coefficients `StrongDual κ E` into the bounded-convergence space
  `E →L[κ] G`. The field `κ` is nontrivially normed; `E` only needs an additive
  group, a module structure and its original topology, while `G` has continuous
  addition and jointly continuous scalar action. Scalar and carrier universes
  are independent. No norm on either module, finite dimension, completeness,
  separation or continuity of the operations on `E` is required. The rank-one
  simp formula and whole-map agreement with Mathlib's algebraic `dualTensorHom`
  after forgetting continuity characterize the forward map; no inverse is
  asserted. The [rectangular real example](AlgebraicDirectLimitsExamples/DualTensorHom.lean)
  reconstructs an independently defined two-to-three operator from its column
  tensor and evaluates it at a nonzero input; a zero-dimensional left-source
  example allows an arbitrary topological right module.
- **Continuous lift and curry compatibility with reassociation.**
  [`TopModuleCat.tensorLiftCLM_lift_eq_comp_tensorAssoc`](AlgebraicDirectLimits/Topology/TensorAssociativity.lean)
  identifies the flat continuous lift of any two-coefficient linear family
  with its iterated lift composed with the canonical tensor associator.
  [`TopModuleCat.tensorCurry_comp_tensorAssoc`](AlgebraicDirectLimits/Topology/TensorAssociativity.lean)
  describes the whole curried family of any outgoing continuous linear map
  after reassociation. The ring is commutative with a supplied topology; both
  coefficients are algebraic and the right and target modules have jointly
  continuous scalar actions, with independent carrier universes. No coefficient
  or Hom topology, finiteness, freeness or separation hypothesis is needed.
  The [examples](AlgebraicDirectLimitsExamples/TensorAssociativity.lean)
  include distinct nonzero coordinate lifts, infinite integer coefficients
  with usual real factors, and a nonfree ideal over a product ring.
- **Arbitrary product coordinates and projective Hausdorff preservation.**
  Over a commutative ring with a supplied topology, let `C` be an algebraic
  coefficient module and `M` a Hausdorff topological module with jointly
  continuous scalar action. For any supplied basis of `C`,
  [`tensorCoordinatesCLM`](AlgebraicDirectLimits/Topology/TensorHom.lean)
  is continuous and injective, and
  [`t2Space_tensorLeftObj_of_basis`](AlgebraicDirectLimits/Topology/TensorSeparation.lean)
  gives Hausdorffness of the one-sided tensor without a finite-basis hypothesis.
  [`t2Space_tensorLeftObj`](AlgebraicDirectLimits/Topology/TensorSeparation.lean)
  gives the same preservation when `C` is projective, using its split free cover.
  Carrier and basis-index universes are independent; no coefficient topology or
  continuity of ring multiplication is required. See the
  [infinite-basis and nonfree projective examples](AlgebraicDirectLimitsExamples/ProjectiveTensorSeparation.lean).
- **Flat coefficients need not preserve tensor Hausdorffness.**
  [`TensorCircleExamples.not_t2Space_rationalCircleTensor`](AlgebraicDirectLimitsExamples/TensorCircleClient.lean)
  proves that `ℚ ⊗[ℤ] AddCircle (1 : ℝ)` is not Hausdorff for the finest
  topological-module topology making every fixed-coefficient generator continuous.
  The rational coefficient module is flat, and the usual real circle is compact
  Hausdorff with jointly continuous integer action. The continuous generator at
  coefficient `1` kills every rational angle, a dense family, but is nonzero at
  `[√2]`. No topology on the coefficients, rational action on the circle or
  continuity of the algebraic detector is used. See the
  [model](AlgebraicDirectLimitsExamples/TensorCircleModel.lean) and
  [detailed counterexample](docs/Results.md#supporting-rational-circle-results).
- **Scalar extension by a discrete coefficient algebra.**
  [`Topology.DiscreteScalarExtension`](AlgebraicDirectLimits/Topology/DiscreteScalarExtension.lean)
  constructs a coefficient-linear topological module over a possibly
  noncommutative discrete `R`-algebra `K`, for a commutative ring `R` with a
  supplied topology and any topological `R`-module. The separate base-linear
  view reuses `tensorLeftObj` exactly; the continuous unit lands in that view.
  Neither coefficient finiteness, input finiteness nor continuity of the algebra
  map is required. Fixed-coefficient continuity gives joint continuity of the
  `K`-action; continuous input maps extend functorially and the unit determines
  outgoing coefficient-linear maps. For commutative `K`, forgetting topology
  gives a natural comparison with Mathlib's algebraic scalar extension.
  The [examples](AlgebraicDirectLimitsExamples/DiscreteScalarExtension.lean)
  use noncommutative matrix coefficients over `ℤ` and a countable-product input,
  with a nonzero tensor moved by extended doubling and order-sensitive actions.
  A rank-one example uses `R = K = ℤ × ℤ` with the swapping algebra map and a
  separately bundled regular input. Its coefficient-linear comparison sends
  `c ⊗ m` to `φ(m) * c`; on the nonzero unit, the two actions of `(1, 0)` have
  images `(0, 1)` and `(1, 0)`. The extended regular-input projection is nonzero
  and differs from the identity.
- **Finite-generation boundary for tensor compactness.**
  Over `R = ZMod 2`, the algebraic coefficient module `C = ℕ →₀ R` is
  countably free and projective but not finitely generated. The discrete right
  self-module `M = R` is nontrivial, compact and Hausdorff, yet
  [`TensorNoncompactness.not_compactSpace_tensor`](AlgebraicDirectLimitsExamples/TensorNoncompactness.lean)
  shows that their one-sided tensor is not compact. The right unitor gives a
  homeomorphism with an infinite discrete comparison module retaining `C`'s
  action; no topology on `C` is an input. Thus finite generation cannot in
  general be omitted from compactness preservation, even for free/projective
  coefficients.
- **Varying scalars and tensor products.**
  [`DirectLimit.VaryingScalar.tensorProductEquiv`](AlgebraicDirectLimits/VaryingScalar.lean#L429)
  identifies the tensor product of two module limits over a *varying*
  commutative-semiring limit with the limit of their stagewise tensor products.
  It uses compatible semilinear module systems over a nonempty directed preorder,
  with four independent universes and no injectivity assumption on transitions.
  See the [module](AlgebraicDirectLimits/VaryingScalar.lean) and
  [representative client](tests/ReadinessClient.lean#L54).
- **Mittag--Leffler inverse systems.**
  [`IsMittagLeffler.nonempty_sections_of_countable_cofinal`](AlgebraicDirectLimits/MittagLeffler.lean#L66)
  gives a compatible section for a pointwise nonempty, Type-valued
  Mittag--Leffler inverse system over a nonempty directed preorder with a
  countable cofinal subset. Under the same index and Mittag--Leffler conditions,
  [`surjective_evalSectionToEventualRange`](AlgebraicDirectLimits/MittagLeffler.lean#L97)
  lifts each element of an eventual range to a section; this second theorem does
  not separately assume pointwise nonemptiness. See the
  [module](AlgebraicDirectLimits/MittagLeffler.lean) and
  [client](tests/ReadinessClient.lean#L142).
- **Prime spectra of filtered colimits.** For a small filtered category and
  any colimit cocone of commutative rings,
  [`PrimeSpectrum.colimitCone_isLimit`](AlgebraicDirectLimits/PrimeSpectrumFilteredColimits.lean)
  identifies its spectrum cone as a limit **in topological spaces**. The
  [chosen-limit homeomorphism and projection law](AlgebraicDirectLimits/PrimeSpectrumFilteredColimits.lean)
  identify each coordinate with contraction along its cocone map. No
  injectivity, nonzero-ring, nonempty-spectrum or separation hypothesis is
  required. See the [constant, quotient and empty-spectrum examples](AlgebraicDirectLimitsExamples/PrimeSpectrumFilteredColimits.lean).
- **Krull dimension under finite-subset capture.** For a family of homomorphisms
  `φ i : A i →+* B` between commutative semirings, if every finite subset of `B`
  lies in the range of one `φ i`, then
  [`ringKrullDim_le_iSup_of_finite_subset_range`](AlgebraicDirectLimits/RingTheory/KrullDimension/FiniteCapture.lean)
  bounds `ringKrullDim B` by `⨆ i, ringKrullDim (A i)`. The family need not be
  directed and the maps need not be injective; dimensions include `⊥` and `⊤`.
  The same [module](AlgebraicDirectLimits/RingTheory/KrullDimension/FiniteCapture.lean)
  gives the bound by subsemirings generated by finite subsets. For any
  subsemiring `C` of `B`,
  [`ringKrullDim_subsemiring_le_iSup_comap_of_finite_subset_range`](AlgebraicDirectLimits/RingTheory/KrullDimension/FiniteCapture.lean)
  bounds `ringKrullDim C` by `⨆ i, ringKrullDim (C.comap (φ i))`, using
  the same finite-subset hypothesis on `B`. See the
  [surjective, polynomial and empty-family examples](AlgebraicDirectLimitsExamples/RingTheory/KrullDimension/FiniteCapture.lean),
  [proper even-variable subsemiring traces](AlgebraicDirectLimitsExamples/RingTheory/KrullDimension/FiniteCaptureTrace.lean)
  and the [aggregate-import client](tests/FiniteCaptureClient.lean).
  The [guide](docs/Guide.md#krull-dimension-under-finite-subset-capture)
  distinguishes one common stage for each finite subset from pointwise capture.
- **Monoidal object classes.** For a strong monoidal functor, the
  [image submonoid](AlgebraicDirectLimits/MonoidalGroupCompletion.lean#L71)
  consists of its *actual* image on additive skeleta. For braided target `D`,
  [`saturation_eq_top_iff`](AlgebraicDirectLimits/MonoidalGroupCompletion.lean#L87)
  identifies its cofinality with every target object acquiring a complement
  isomorphic to a source-image object. Under this object-cofinality condition,
  there are object denominators and stabilization. If, additionally, the source
  is braided and the functor is fully faithful,
  [`completionMap_injective`](AlgebraicDirectLimits/MonoidalGroupCompletion.lean#L230)
  makes the induced completion map injective; the
  [additive equivalence](AlgebraicDirectLimits/MonoidalGroupCompletion.lean#L238)
  is to its *range*, not necessarily the whole target completion. Neither
  cancellation nor essential surjectivity is needed. See the
  [module](AlgebraicDirectLimits/MonoidalGroupCompletion.lean) and
  [client](tests/MonoidalGroupCompletionClient.lean#L169).

The [selected detailed result descriptions](docs/Results.md) retain hypotheses,
examples and limitations for the results described there. They also describe the
[rational-circle counterexample and supporting APIs](docs/Results.md#supporting-rational-circle-results),
including the algebraic detector, nonzero irrational tensor and rational-angle laws.

## Tensor–Hom naturality

[`tensorLiftCLM_comp_tensorMapCLM`](AlgebraicDirectLimits/Topology/TensorHom.lean)
states that lifting a family after coefficient and continuous right-input
precomposition equals precomposing its lift by the tensor map.
[`tensorCurry_comp`](AlgebraicDirectLimits/Topology/TensorHom.lean) states that
currying after outgoing postcomposition postcomposes the entire curried family.
These are whole-map equalities for arbitrary bundled maps, over a commutative
ring with a supplied topology and topological modules with jointly continuous
scalar actions. Their six and five carrier universes, respectively, are
independent; no coefficient or Hom topology, finiteness, freeness or separation
hypothesis is added.

The [naturality examples](AlgebraicDirectLimitsExamples/TensorHomNaturality.lean)
state six whole-map specializations and three variable mixed-tensor formulas,
using integer axis restrictions and doubling, infinite integer coefficients
with usual real right factors and product-coordinate readouts, and a nonfree
ideal over `ℤ × ℤ`. The module constructs
the input maps with existing linear/continuous constructors and combines
existing nonzero, distinct, nonfinite, nondiscrete and nonfree proof values.
See the [detailed statements and algebraic comparison](docs/Results.md#tensorhom-naturality).

## Using the library

To use the library in another project with a matching Lean toolchain, add this
dependency to your `lakefile.toml`:

```toml
[[require]]
name = "algebraic-direct-limits"
git = "https://github.com/FormalFrontier/algebraic-direct-limits.git"
rev = "main"
```

GitHub `main` contains only reviewed releases. Lake resolves the latest release
when you first add or update the dependency;
`lake-manifest.json` retains that commit until the next update. To pin a specific
release, replace `main` with its full commit from the
[public history](https://github.com/FormalFrontier/algebraic-direct-limits).
Import the aggregate with `import AlgebraicDirectLimits`, or the linked leaf
appropriate to your use. No private research workspace is needed.

For a first use, follow
[`tensor_equiv_on_representatives`](tests/ReadinessClient.lean#L54) or
[`cofinal_restriction_without_nonempty`](tests/ReadinessClient.lean#L121).
The headline links also provide examples and boundary clients; client
namespaces are not public library declarations.

Use one revision of this package in a build. When combining it with other
Lean libraries, use releases built against a common Mathlib revision; Lake
resolves one revision of each package, not separate copies for each dependency.

Arbitrary product coordinates detect equality, but do not supply an
infinite-product inverse or surjectivity; finite-coordinate equivalences and
finite-sum inverses remain finite-only. Projective Hausdorff preservation does
not imply reflection or finite generation. The compactness theorem assumes finitely
generated coefficients and a compact right factor. The
[noncompact tensor example](AlgebraicDirectLimitsExamples/TensorNoncompactness.lean)
shows that finite generation cannot in general be omitted, even with countably
free/projective coefficients and a nontrivial compact Hausdorff right factor.
Full categorical tensor
coherence, a pentagon construction and completed tensor products are outside
this API. The rational-circle counterexample rules out Hausdorff preservation
for arbitrary flat coefficients. Basis change remains a type contract.

## Modules

| Module | Contents |
| --- | --- |
| [`VaryingScalar`](AlgebraicDirectLimits/VaryingScalar.lean) | Module and tensor-product limits over varying scalars |
| [`Topology.Coinduced`](AlgebraicDirectLimits/Topology/Coinduced.lean) | Generator criterion for linear continuity from coinduced topological modules |
| [`Topology.StrongDual`](AlgebraicDirectLimits/Topology/StrongDual.lean) | Module topology on finite-dimensional continuous duals without complete scalars |
| [`AlgebraicDirectLimitsExamples.StrongDual`](AlgebraicDirectLimitsExamples/StrongDual.lean) | Rational-plane application, dimension-zero boundary and complete-field agreement |
| [`Topology.Restriction`](AlgebraicDirectLimits/Topology/Restriction.lean) | Same-topology scalar restriction, natural identity/composition comparisons and a regular-action continuity criterion |
| [`Topology.RestrictionKernels`](AlgebraicDirectLimits/Topology/RestrictionKernels.lean) | Additivity and preservation of each kernel under continuous scalar restriction |
| [`Topology.RestrictionCokernels`](AlgebraicDirectLimits/Topology/RestrictionCokernels.lean) | Preservation of algebraic-range cokernels and their universal property for arbitrary smaller-ring targets |
| [`Topology.DiscreteScalarExtension`](AlgebraicDirectLimits/Topology/DiscreteScalarExtension.lean) | Discrete coefficient-algebra scalar extension, continuous unit and functorial maps with separate scalar views |
| [`Topology.TensorProduct`](AlgebraicDirectLimits/Topology/TensorProduct.lean) | One-sided tensor topology, linear continuity, continuous tensor maps, linearity in each map variable and finite-basis contracts |
| [`Topology.TensorFunctor`](AlgebraicDirectLimits/Topology/TensorFunctor.lean) | Additive tensor functor with fixed algebraic coefficients, the one-sided topology, algebraic map compatibility and pure-tensor values |
| [`AlgebraicDirectLimitsExamples.TensorFunctor`](AlgebraicDirectLimitsExamples/TensorFunctor.lean) | Integer doubling compatibility and the additive functor law evaluated on a nonzero rank-two tensor |
| [`Topology.TensorBifunctor`](AlgebraicDirectLimits/Topology/TensorBifunctor.lean) | Tensor functor in algebraic coefficients and topological right modules, with characteristic uncurried maps and fixed-slot equalities |
| [`AlgebraicDirectLimitsExamples.TensorBifunctor`](AlgebraicDirectLimitsExamples/TensorBifunctor.lean) | Coefficient doubling and right tripling on the integer unit tensor, detected as six and nonzero |
| [`AlgebraicDirectLimitsExamples.TensorProduct.Map`](AlgebraicDirectLimitsExamples/TensorProduct/Map.lean) | Infinite-rank integer coefficient projections with nonzero two-term inputs, distinct supported outputs, unequal weights, and whole-map finite-sum laws |
| [`Topology.TensorProduct.Prod`](AlgebraicDirectLimits/Topology/TensorProduct/Prod.lean) | Binary-product distribution for an algebraic coefficient module and two topological right factors over a commutative ring with a supplied topology; ordinary product topology, independent carrier universes and naturality in algebraic coefficient and continuous right-factor maps |
| [`AlgebraicDirectLimitsExamples.TensorProduct.Prod`](AlgebraicDirectLimitsExamples/TensorProduct/Prod.lean) | Infinite-rank integer Finsupp coefficients and the usual real product, with independently supported tensors, reconstruction and map detectors |
| [`Topology.TensorProduct.Quotient`](AlgebraicDirectLimits/Topology/TensorProduct/Quotient.lean) | Continuous tensor-quotient equivalence for algebraic coefficients and arbitrary submodules, with arbitrary- and pure-tensor forward/inverse formulas |
| [`AlgebraicDirectLimitsExamples.CoefficientTensorQuotient`](AlgebraicDirectLimitsExamples/CoefficientTensorQuotient.lean) | Rank-two mod-two torsion and infinite integer coefficients, quotient block maps, distinct-index detectors, doubling controls and a nonclosed rational submodule |
| [`Topology.TensorDiscrete`](AlgebraicDirectLimits/Topology/TensorDiscrete.lean) | Joint scalar continuity at bottom and discrete canonical tensors with arbitrary algebraic coefficients and a discrete right module |
| [`AlgebraicDirectLimitsExamples.DiscreteTensor`](AlgebraicDirectLimitsExamples/DiscreteTensor.lean) | Non-finitely-generated mod-two integer coefficients, nondiscrete product-ring scalars, joint restricted actions and algebraic nonzero/distinct/mixed tensor detectors |
| [`Topology.TensorCompactness`](AlgebraicDirectLimits/Topology/TensorCompactness.lean) | Compactness of one-sided tensors with finitely generated coefficients |
| [`Topology.TensorHom`](AlgebraicDirectLimits/Topology/TensorHom.lean) | Continuous tensor lift, curry, universal-property linear equivalence, arbitrary product coordinates and lift/curry naturality |
| [`Topology.DualTensorHom`](AlgebraicDirectLimits/Topology/DualTensorHom.lean) | Continuous dual tensor contraction into bounded-convergence Hom, rank-one simp formula and algebraic agreement |
| [`AlgebraicDirectLimitsExamples.DualTensorHom`](AlgebraicDirectLimitsExamples/DualTensorHom.lean) | Independently constructed rectangular real operator, column-tensor reconstruction, nonzero value and zero-dimensional left-source boundary |
| [`Topology.CoefficientTensor`](AlgebraicDirectLimits/Topology/CoefficientTensor.lean) | Coefficient tensor–continuous Hom adjunction over a commutative ring equipped with a topology, characteristic currying equivalence and preservation of existing colimits |
| [`AlgebraicDirectLimitsExamples.CoefficientTensor`](AlgebraicDirectLimitsExamples/CoefficientTensor.lean) | Infinite, nonfree and distinct-action coefficient models, with nonzero integer evaluations of coefficient and target naturality |
| [`AlgebraicDirectLimitsExamples.CoefficientTensorAdjunction`](AlgebraicDirectLimitsExamples/CoefficientTensorAdjunction.lean) | Nonzero counit evaluation on integer endomorphisms and preservation of their canonical binary coproduct |
| [`AlgebraicDirectLimitsExamples.TensorHomNaturality`](AlgebraicDirectLimitsExamples/TensorHomNaturality.lean) | Integer-axis, infinite-real-coordinate and nonfree-ideal naturality laws, variable mixed-tensor formulas and nonzero control values |
| [`Topology.TensorUnit`](AlgebraicDirectLimits/Topology/TensorUnit.lean) | Continuous scalar tensor unit and right-factor naturality |
| [`Topology.TensorAssociativity`](AlgebraicDirectLimits/Topology/TensorAssociativity.lean) | Continuous reassociation of one-sided tensor products, three-factor naturality and whole lift/curry compatibility |
| [`Topology.TensorSeparation`](AlgebraicDirectLimits/Topology/TensorSeparation.lean) | Arbitrary-basis and projective Hausdorff preservation |
| [`Topology.TensorCircle.Detector`](AlgebraicDirectLimits/Topology/TensorCircle/Detector.lean) | Algebraic rational-quotient detector and a nonzero irrational pure tensor |
| [`Topology.TensorCircle.RationalAngles`](AlgebraicDirectLimits/Topology/TensorCircle/RationalAngles.lean) | Dense rational angles, positive integer annihilators and vanishing rational pure tensors |
| [`AlgebraicDirectLimitsExamples.TensorCircleModel`](AlgebraicDirectLimitsExamples/TensorCircleModel.lean) | Flat rational coefficients, the usual compact Hausdorff circle and its continuous tensor generator |
| [`AlgebraicDirectLimitsExamples.TensorCircleClient`](AlgebraicDirectLimitsExamples/TensorCircleClient.lean) | Non-Hausdorff rational-circle tensor, detector and generator laws, a nonzero killed half-angle and combined supporting properties |
| [`Order.DirectedSystem`](AlgebraicDirectLimits/Order/DirectedSystem.lean) | Constant families with identity transition functions over arbitrary preorders |
| [`RingTheory.DirectLimit`](AlgebraicDirectLimits/RingTheory/DirectLimit.lean) | Constant identity ring-homomorphism systems over arbitrary preorders and nonassociative semirings |
| [`AlgebraicDirectLimitsTests.Topology.TensorProduct`](tests/AlgebraicDirectLimitsTests/Topology/TensorProduct.lean) | Type contracts for linear continuity, tensor maps, finite-basis coordinates, basis change and preservation properties |
| [`CofinalSequence`](AlgebraicDirectLimits/CofinalSequence.lean) | Countably cofinal directed indices |
| [`MittagLeffler`](AlgebraicDirectLimits/MittagLeffler.lean) | Compatible sections of inverse systems |
| [`SimpleRing`](AlgebraicDirectLimits/SimpleRing.lean) | Filtered colimits of simple rings |
| [`PrimeSpectrumFilteredColimits`](AlgebraicDirectLimits/PrimeSpectrumFilteredColimits.lean) | Topological limits of filtered-colimit prime spectra |
| [`RingTheory.KrullDimension.FiniteCapture`](AlgebraicDirectLimits/RingTheory/KrullDimension/FiniteCapture.lean) | Finite-subset capture, strict prime chains and Krull-dimension bounds for semirings and subsemiring preimages |
| [`RingTheory.KrullDimension.DirectLimit`](AlgebraicDirectLimits/RingTheory/KrullDimension/DirectLimit.lean) | Directed-colimit dimension bound without injective transitions |
| [`RingTheory.KrullDimension.DirectedUnion`](AlgebraicDirectLimits/RingTheory/KrullDimension/DirectedUnion.lean) | Dimension bound for nonempty inclusion-directed subsemiring unions |
| [`LocalizationPi`](AlgebraicDirectLimits/LocalizationPi.lean) | Localization and countable products |
| [`CofinalGroupCompletion`](AlgebraicDirectLimits/CofinalGroupCompletion.lean) | Group completions at cofinal submonoids |
| [`MonoidalGroupCompletion`](AlgebraicDirectLimits/MonoidalGroupCompletion.lean) | Object classes under strong monoidal functors |
| [`GradedStabilization`](AlgebraicDirectLimits/GradedStabilization.lean) | Graded normalization and kernel criteria |

The [mathematical guide](docs/Guide.md) explains the constructions and proofs;
the Lean modules give the exact signatures and hypotheses. The
[partial API reference](docs/API.md) selects **73 library and 23 boundary-client
sites from seven mathematical modules**; [its overview](docs/README.md) lists
those modules. It does not cover `Order.DirectedSystem`, `RingTheory.DirectLimit`,
`MonoidalGroupCompletion`,
`PrimeSpectrumFilteredColimits`, `Topology.Coinduced`, `Topology.StrongDual`,
`Topology.TensorProduct`,
`Topology.TensorDiscrete`, `Topology.TensorProduct.Prod`, `Topology.Restriction`,
`Topology.RestrictionKernels`, `Topology.RestrictionCokernels`,
`Topology.DiscreteScalarExtension`, `Topology.TensorHom`, `Topology.DualTensorHom`,
`Topology.TensorUnit`,
`Topology.TensorAssociativity`, `Topology.TensorCompactness`,
`Topology.TensorSeparation`, `Topology.TensorCircle.Detector`,
`Topology.TensorCircle.RationalAngles`,
`RingTheory.KrullDimension.FiniteCapture`, `RingTheory.KrullDimension.DirectLimit`,
`RingTheory.KrullDimension.DirectedUnion`, aggregate/test roots or all
private/generated declarations.
Use the module source and guide for omitted material; client namespaces are not
re-exported as library APIs. This library does not claim a complete theory of
limits or formal coverage of a specific mathematical source.

## Reproduce

The [Lean toolchain](lean-toolchain), [Lake package](lakefile.toml) and
[manifest](lake-manifest.json) record the build environment and resolved
dependencies. Mathlib is the sole direct dependency. With network access, run
from the repository root, **fetching the matching precompiled mathlib cache
successfully before any build**:

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
lake exe cache get
lake --wfail build
```

The default targets in [`lakefile.toml`](lakefile.toml) are the aggregate,
`AlgebraicDirectLimitsExamples` and [`ReadinessTests`](tests/ReadinessTests.lean),
which imports the registered standalone clients. Together these targets cover
35 mathematical leaf modules plus the public aggregate (36 library modules), 32 example modules and seven test modules: 75 local modules in the default source import closure.
The coefficient-tensor API includes characteristic identities for concrete Hom, tensor maps, currying, and naturality in algebraic coefficients and continuous targets. The circle library
modules are imported by the circle clients, not by the public aggregate.
To check one module or client after the cache succeeds:

```sh
lake --wfail build AlgebraicDirectLimits.MonoidalGroupCompletion
lake env lean -DwarningAsError=true tests/ReadinessClient.lean
```

## Build resources

Allow resource headroom for the matching Mathlib cache and concurrent Lean jobs.
When resources are constrained, check one target at a time. If the matching
cache fetch fails, resolve that failure before building; do not fall back to a
full Mathlib source build.

## References and credits

The [Stacks Project, Algebra, Lemma 10.86.3](https://stacks.math.columbia.edu/tag/0597)
is a mathematical reference for nonempty Mittag--Leffler inverse limits over
countable indices. The present countable-*cofinal*-subset theorem has a different
index hypothesis and is not a claim of verbatim translation or source coverage.
The [Stacks Project, Algebra, Section 10.8](https://stacks.math.columbia.edu/tag/07N7)
provides mathematical background on filtered colimits; specific source
correspondences, if any, require separate assessment. The modules reuse
constructions in [mathlib4](https://github.com/leanprover-community/mathlib4),
including `Mathlib.Algebra.Colimit.DirectLimit`,
`Mathlib.CategoryTheory.Filtered.Final`,
`Mathlib.CategoryTheory.CofilteredSystem`,
`Mathlib.Algebra.Category.Ring.FilteredColimits` and
`Mathlib.RingTheory.Localization.Pi`. References are mathematical background,
not quotations or claims of formalizing those exact texts.

Original contributions by Formal Frontier Agents include varying scalars,
cofinality and Mittag--Leffler systems; simple-ring colimits, graded
stabilization and monoidal research; and distinct Lean implementations for
localization, cofinal completion and monoidal completion. Formal Frontier Agents
also contributed library assembly and subsequent improvements. See
[contributors and provenance](docs/CREDITS.md) for details; these are AI-assisted
formal developments, not claims of source-author endorsement. The finite-capture
dimension bounds are a formal development by Formal Frontier Agents using
Mathlib's `Order.krullDim`, `LTSeries` and `PrimeSpectrum.comap`; the singleton
family recovers Mathlib's `ringKrullDim_le_of_surjective`. The directed-colimit
specialization and its models are also due to Formal Frontier Agents, using
Mathlib's characteristic maps, representatives and directed finite-union capture API.
The constant-identity directed-system instances generalize the integer client
law developed by Formal Frontier Agents, using Junyan Xu's Mathlib
`DirectedSystem` and its identity and composition API.
`DirectedSystem.constRingHom` specializes the same function-law witness using
the identity-coercion API of Amelia Livingston and Jireh Loreaux.
It allows any nonassociative semiring over an arbitrary preorder, independently
of the directedness and nonemptiness required by the colimit.
The directed-subsemiring union bound and its models use the same finite-capture
criterion, Mathlib's subsemiring union and inclusion API, and the integer and
rational dimension theorems.
The coinduced-module criterion follows Richard Hill and Andrew
Yang's Mathlib coinduced construction and `TopModuleCat.isColimit`
induced-topology proof. The same-topology restriction generalizes the restriction
object and continuous-map construction in Continuous Group Cohomology, including
Formal Frontier Agents' original restriction and continuous-map development.
Its algebraic objects and comparisons reuse Jujian Zhang's Mathlib change-of-rings
API; continuous maps reuse Sébastien Gouëzel and Yury Kudryashov's restriction
API. The regular-action continuity criterion
and Algebra agreement follow Mathlib's `continuous_algebraMap_iff_smul` and
`Algebra.smul_def`; the former is from the topological-algebra development by
Kim Morrison, Antoine Chambert-Loir and María Inés de Frutos-Fernández.
The kernel and cokernel preservation modules reuse Mathlib's additive-functor,
forgetful-limit reflection and quotient-comparison APIs; their module references
credit the underlying topological-module constructions and formalization approach.
The finite-dimensional strong-dual theorem uses Kevin Buzzard and Will Sawin's
module-topology constructions, Mathlib's finite-dimensional basis API, and
Anatole Dedecker and Yury Kudryashov's bounded-convergence topology.
The one-sided tensor topology follows
scalar-extension ideas from
[Continuous Group Cohomology](https://github.com/FormalFrontier/continuous-group-cohomology)
by Formal Frontier Agents, including the original topological development.
Its local universe adapters reuse Mathlib's module and continuous-linear `ULift`
APIs directly. The continuous tensor universal property and scalar unit reuse
Kenny Lau and Mario Carneiro's Mathlib algebraic tensor lift, lift equivalence
and scalar unit; continuity is supplied by the fixed-coefficient generator
criterion. The complementary lift-precomposition statement represents Mathlib's
`TensorProduct.lift_comp_map` in the continuous map space for the existing
one-sided topology, rather than asserting a new algebraic naturality theorem.
The modules name the contributors to their continuous-linear APIs.
The continuous dual tensor contraction follows Formal Frontier Agents' dual-tensor
construction, applying Oliver Nash and Antoine Labelle's Mathlib algebraic
contraction and Anatole Dedecker and Yury Kudryashov's bounded-convergence
precomposition and scalar-line APIs through the existing one-sided tensor lift.
The coefficient tensor–continuous Hom adjunction follows Formal Frontier Agents'
coefficient tensor formulation and Mathlib's adjunction and colimit-preservation
interfaces.
The two-variable tensor functor combines the one-variable constructions,
including the coinduced topology and tensor models developed by Formal Frontier
Agents, and reuses Mathlib's functor currying and flipping interfaces by
Kim Morrison, Tim Baumann, Stephen Morgan and Floris van Doorn. Its tensor maps
reuse Kenny Lau and Mario Carneiro's algebraic tensor-map API.
The arbitrary-basis/projective preservation follows Formal Frontier Agents'
split-cover mathematics, reusing Kevin Buzzard and Antoine Labelle's
projective-module API, Mathlib's Finsupp and tensor-basis APIs,
Johan Commelin's infinite-basis finiteness provider, and Johannes Hölzl,
Mario Carneiro and Yury Kudryashov's dense-order topology. The fixed product-ring
ideal model uses Kenny Lau, Chris Hughes and Mario Carneiro's ideal API. Related general idempotent-ideal mathematics is
provided by [Projective Modules](https://github.com/FormalFrontier/projective-modules),
including Formal Frontier Agents' work on projective modules; no dependency on
that library or new general ideal API is introduced here.
The discrete-right tensor statements generalize the Continuous Group Cohomology
discrete-tensor scalar provider to arbitrary algebraic coefficients and reuse
Mathlib's discrete-topology continuity APIs by Johannes Hölzl, Mario Carneiro
and Mitchell Lee.
The rational-circle constructions and non-Hausdorffness proof follow Formal
Frontier Agents, *Rational coefficients do not preserve tensor
Hausdorffness*, and its stock API companion. They reuse Mathlib's localization
flatness, Oliver Nash's additive circle, integer tensor balancing, rational cast
density, irrationality of `Real.sqrt 2` and uniqueness of continuous maps on a
dense set; the four linked circle modules give the detailed contributor and
proof-route credits.
The [Apache-2.0 license](LICENSE) covers original project material;
mathlib and the other separately maintained dependencies keep their own licenses
and notices. Collective author credit alone does not establish legal ownership
or resolve third-party rights concerns.
