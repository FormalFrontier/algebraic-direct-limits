# Algebraic Direct Limits

Authors: Formal Frontier Agents. License: [Apache-2.0](LICENSE).

This library works with mathlib's native directed limits, localizations,
Grothendieck group completions and categorical colimits. Import the
[public aggregate](AlgebraicDirectLimits.lean) with `import AlgebraicDirectLimits`,
or import any of the eighteen mathematical modules individually.

## Headline results

- **Same-topology scalar restriction.**
  [`TopModuleCat.restrictScalarsObj`](AlgebraicDirectLimits/Topology/Restriction.lean)
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
  [coordinate-swap, matrix, semiring and Algebra clients](AlgebraicDirectLimitsExamples/Restriction.lean).
- **One-sided tensor topology.**
  [`TopModuleCat.tensorLeftObj`](AlgebraicDirectLimits/Topology/TensorProduct.lean)
  equips `C ⊗[R] M` with the coinduced topological-module topology for every
  `m ↦ c ⊗ₜ m`, over a commutative ring with a supplied topology. Only `M` is
  topological; neither factor has a finiteness hypothesis. Linear continuity out
  of the tensor is characterized by its continuous fixed-coefficient generators.
  The canonical `tensorMapCLM` realizes `TensorProduct.map` for an algebraic
  left-factor map and continuous right-factor map, with application, identity
  and composition laws. Finite-basis coordinates give a continuous linear
  equivalence with the finite product of `M`; the inverse reconstructs tensors
  by summing continuous basis generators. The scalar ring may be trivial and
  the basis index may be empty. Basis change and compactness characterizations
  remain type contracts, not proved results.
  See the
  [integer-pair and boundary examples](AlgebraicDirectLimitsExamples/TensorProduct.lean).
- **Finite-basis tensor Hausdorffness.**
  [`TopModuleCat.t2Space_tensorLeftObj_of_basis`](AlgebraicDirectLimits/Topology/TensorSeparation.lean)
  proves Hausdorff preservation with a finite coefficient basis, and
  `t2Space_tensorLeftObj` gives its finite-free specialization. Both use the
  continuous finite-product coordinates for the existing one-sided tensor
  topology over an arbitrary commutative ring with a supplied topology, without
  a coefficient topology, finiteness of the right module or continuity of ring
  multiplication. The
  [separation examples](AlgebraicDirectLimitsExamples/TensorSeparation.lean)
  use integer-pair coefficients, the nonfree integer module `ZMod 3`, nonzero
  pure and mixed tensors, and the noncompact Hausdorff integer right factor.
  Empty and trivial coefficient cases illustrate why no converse is stated.
  Preservation for arbitrary projective coefficients and compactness remain
  outside these results.
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
- **Continuous scalar tensor unit.**
  [`TopModuleCat.tensorUnitContinuousLinearEquiv`](AlgebraicDirectLimits/Topology/TensorUnit.lean)
  equips Mathlib's `TensorProduct.lid R M` with the one-sided tensor topology:
  `r ⊗ₜ m` maps to `r • m`, and its inverse is the continuous generator
  `m ↦ 1 ⊗ₜ m`. It is natural in continuous right-factor maps, over any
  commutative ring with a supplied topology and jointly continuous action on
  `M`, without continuity of ring multiplication or a finite basis. See the
  [integer-pair doubling examples](AlgebraicDirectLimitsExamples/TensorUnit.lean).
- **Varying scalars and tensor products.**
  [`DirectLimit.VaryingScalar.tensorProductEquiv`](AlgebraicDirectLimits/VaryingScalar.lean#L429)
  identifies the tensor product of two module limits over a *varying*
  commutative-semiring limit with the limit of their stagewise tensor products.
  It uses compatible semilinear module systems over a nonempty directed preorder,
  with four independent universes and no injectivity assumption on transitions.
  See the [module](AlgebraicDirectLimits/VaryingScalar.lean) and
  [representative client](tests/ReadinessClient.lean#L48).
- **Coinduced topological modules.**
  [`TopModuleCat.continuous_coinduced_iff`](AlgebraicDirectLimits/Topology/Coinduced.lean)
  characterizes continuity of a linear map out of Mathlib's existing coinduced
  topological module by continuity on every generator. It needs only a ring
  with a supplied topology, allows an empty index type and an independently
  leveled target, and does not assert a nonlinear final-topology property.
  The [examples](AlgebraicDirectLimitsExamples/Coinduced.lean) use the two integer
  axes in `ℤ × ℤ` and the nonzero functional `(x, y) ↦ x + 2 * y`; addition on
  a product is also treated over a possibly noncommutative ring.
- **Sequentializing cofinality.**
  [`IsCofinal.exists_monotone_nat`](AlgebraicDirectLimits/CofinalSequence.lean#L33)
  and [`exists_final_functor_nat`](AlgebraicDirectLimits/CofinalSequence.lean#L55)
  produce a monotone cofinal sequence and a final functor from `ℕ` when a
  *nonempty directed preorder has a countable cofinal subset*; the entire index
  type need not be countable. See the [module](AlgebraicDirectLimits/CofinalSequence.lean)
  and [client](tests/ReadinessClient.lean#L100).
- **Mittag--Leffler inverse systems.**
  [`IsMittagLeffler.nonempty_sections_of_countable_cofinal`](AlgebraicDirectLimits/MittagLeffler.lean#L66)
  gives a compatible section for a pointwise nonempty, Type-valued
  Mittag--Leffler inverse system over a nonempty directed preorder with a
  countable cofinal subset. Under the same index and Mittag--Leffler conditions,
  [`surjective_evalSectionToEventualRange`](AlgebraicDirectLimits/MittagLeffler.lean#L97)
  lifts each element of an eventual range to a section; this second theorem does
  not separately assume pointwise nonemptiness. See the
  [module](AlgebraicDirectLimits/MittagLeffler.lean) and
  [client](tests/ReadinessClient.lean#L136).
- **Filtered colimits of simple rings.**
  [`RingCat.FilteredColimits.colimit_isSimpleRing`](AlgebraicDirectLimits/SimpleRing.lean#L47)
  proves that a small filtered colimit of simple rings in the possibly
  noncommutative `RingCat` is simple. Stage-map injectivity follows from
  simplicity; it is not a diagram hypothesis. See the
  [module](AlgebraicDirectLimits/SimpleRing.lean) and
  [client](tests/ReadinessClient.lean#L156).
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
- **Krull dimension of directed colimits.** For commutative semirings over a
  nonempty directed preorder, with compatible ring-homomorphism transitions,
  [`ringKrullDim_directLimit_le_iSup`](AlgebraicDirectLimits/RingTheory/KrullDimension/DirectLimit.lean)
  bounds the dimension of `DirectLimit G f` by `⨆ i, ringKrullDim (G i)`.
  The index and stage universes are independent. No injectivity, Noetherianity,
  domain, nontriviality or finite-dimension hypothesis is needed; dimensions
  retain `⊥` and `⊤`. The proof applies finite-subset capture to the canonical
  stage maps. See the [constant integer and noninjective quotient models](AlgebraicDirectLimitsExamples/RingTheory/KrullDimension/DirectLimit.lean).
- **Krull dimension of directed subsemiring unions.** For a nonempty family
  `s : ι → Subsemiring R` in a commutative semiring, directed under inclusion,
  [`Subsemiring.ringKrullDim_iSup_le`](AlgebraicDirectLimits/RingTheory/KrullDimension/DirectedUnion.lean)
  bounds `ringKrullDim (⨆ i, s i : Subsemiring R)` by `⨆ i, ringKrullDim (s i)`.
  The index needs no order, and its universe is independent of the ambient
  semiring's. No Noetherianity, domain, nontriviality or finite-dimension
  hypothesis is needed; dimension values include `⊥` and `⊤`. The proof uses
  canonical inclusions and finite-subset capture. See the
  [proper integer-to-rational family and empty-index boundary](AlgebraicDirectLimitsExamples/RingTheory/KrullDimension/DirectedUnion.lean).
  This is only an upper bound: the proper two-stage family indexed by `Bool`
  in `ℚ` has stage-dimension supremum one and union dimension zero.
- **Localization of a countable product.**
  [`Localization.awayPiComparison`](AlgebraicDirectLimits/LocalizationPi.lean#L26)
  compares localization of `ℕ → R` at a constant `r` with the countable product
  of localizations of `R` away from `r`.
  [`awayPiComparison_not_surjective`](AlgebraicDirectLimits/LocalizationPi.lean#L50)
  shows non-surjectivity if `R` is a commutative domain and `r` is nonzero and
  not a unit; no finite-product claim follows. See the
  [module](AlgebraicDirectLimits/LocalizationPi.lean) and
  [client](tests/ReadinessClient.lean#L166).
- **Cofinal submonoids and group completion.** If an additive submonoid `L`
  of an arbitrary additive commutative monoid has top saturation, the canonical
  completion map [localizes at `L`](AlgebraicDirectLimits/CofinalGroupCompletion.lean#L31).
  This supplies [denominators](AlgebraicDirectLimits/CofinalGroupCompletion.lean#L57),
  [a stabilization test for equal images](AlgebraicDirectLimits/CofinalGroupCompletion.lean#L64)
  and [injectivity on completion of the inclusion](AlgebraicDirectLimits/CofinalGroupCompletion.lean#L71).
  No cancellation is assumed. See the
  [module](AlgebraicDirectLimits/CofinalGroupCompletion.lean) and
  [client](tests/CofinalGroupCompletionClient.lean#L41).
- **Monoidal object classes.** For a strong monoidal functor, the
  [image submonoid](AlgebraicDirectLimits/MonoidalGroupCompletion.lean#L71)
  consists of its *actual* image on additive skeleta. For braided target `D`,
  [`saturation_eq_top_iff`](AlgebraicDirectLimits/MonoidalGroupCompletion.lean#L87)
  identifies its cofinality with every target object acquiring a complement
  isomorphic to a source-image object, giving object denominators and
  stabilization. If the source is also braided and the functor is fully
  faithful, [`completionMap_injective`](AlgebraicDirectLimits/MonoidalGroupCompletion.lean#L230)
  makes the induced completion map injective; the
  [additive equivalence](AlgebraicDirectLimits/MonoidalGroupCompletion.lean#L238)
  is to its *range*, not necessarily the whole target completion. Neither
  cancellation nor essential surjectivity is needed. See the
  [module](AlgebraicDirectLimits/MonoidalGroupCompletion.lean) and
  [client](tests/MonoidalGroupCompletionClient.lean#L169).
- **Graded stabilization.** For `d : M →+ A` and `u : M`,
  [normalization](AlgebraicDirectLimits/GradedStabilization.lean#L112)
  sends the native limit of fibers `d m = n • d u` to the kernel of the induced
  group-completion degree map. Top saturation of the multiples of `u` gives
  [injectivity](AlgebraicDirectLimits/GradedStabilization.lean#L158);
  **cancellation in the degree target `A` only** additionally gives
  [surjectivity](AlgebraicDirectLimits/GradedStabilization.lean#L195)
  and [`normalizationEquiv`](AlgebraicDirectLimits/GradedStabilization.lean#L210),
  an equivalence **of types**, not an additive equivalence. Source monoid
  cancellation and injective transitions are not required. See the
  [module](AlgebraicDirectLimits/GradedStabilization.lean) and
  [boundary client](tests/GradedStabilizationClient.lean#L125).

## Modules

| Module | Contents |
| --- | --- |
| [`VaryingScalar`](AlgebraicDirectLimits/VaryingScalar.lean) | Module and tensor-product limits over varying scalars |
| [`Topology.Coinduced`](AlgebraicDirectLimits/Topology/Coinduced.lean) | Generator criterion for linear continuity from coinduced topological modules |
| [`Topology.Restriction`](AlgebraicDirectLimits/Topology/Restriction.lean) | Same-topology scalar restriction, natural identity/composition comparisons and a regular-action continuity criterion |
| [`Topology.TensorProduct`](AlgebraicDirectLimits/Topology/TensorProduct.lean) | One-sided tensor topology, linear continuity, continuous tensor maps and finite-basis contracts |
| [`Topology.TensorHom`](AlgebraicDirectLimits/Topology/TensorHom.lean) | Continuous tensor lift, curry and universal-property linear equivalence |
| [`Topology.TensorUnit`](AlgebraicDirectLimits/Topology/TensorUnit.lean) | Continuous scalar tensor unit and right-factor naturality |
| [`Topology.TensorSeparation`](AlgebraicDirectLimits/Topology/TensorSeparation.lean) | Finite-basis and finite-free Hausdorff preservation |
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
those modules. It does not cover `MonoidalGroupCompletion`,
`PrimeSpectrumFilteredColimits`, `Topology.Coinduced`, `Topology.TensorProduct`,
`Topology.Restriction`, `Topology.TensorHom`, `Topology.TensorUnit`,
`Topology.TensorSeparation`,
`RingTheory.KrullDimension.FiniteCapture`, `RingTheory.KrullDimension.DirectLimit`,
`RingTheory.KrullDimension.DirectedUnion`, aggregate/test roots or all
private/generated declarations.
Use the module source and guide for omitted material; client namespaces are not
re-exported as library APIs. This library does not claim a complete theory of
limits or formal coverage of a specific mathematical source.

## Reproduce

The [Lean toolchain](lean-toolchain) is `leanprover/lean4:v4.34.0-rc2`; the
[Lake package](lakefile.toml) and [manifest](lake-manifest.json) pin mathlib to
`83abb3e776bdefcbc447a1e44d0debe4010039e5` and resolve its transitive
packages. Mathlib is the sole direct dependency. With network access (and
authorized GitHub access if the distribution is private), run from the
repository root, **fetching the matching precompiled mathlib cache successfully
before any build**:

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
lake exe cache get
lake --wfail build
```

The default targets in [`lakefile.toml`](lakefile.toml) are the aggregate,
`AlgebraicDirectLimitsExamples` and [`ReadinessTests`](tests/ReadinessTests.lean),
which imports the registered standalone clients. They include all eighteen
mathematical modules, eleven example modules and six test modules. To check one
module or client after the cache succeeds:

```sh
lake --wfail build AlgebraicDirectLimits.MonoidalGroupCompletion
lake env lean -DwarningAsError=true tests/ReadinessClient.lean
```

To use the library in another project with a matching Lean toolchain, add this
dependency to your `lakefile.toml`:

```toml
[[require]]
name = "algebraic-direct-limits"
git = "https://github.com/FormalFrontier/algebraic-direct-limits.git"
rev = "main"
```

Lake resolves GitHub `main` when you add or update the dependency;
`lake-manifest.json` retains that commit until the next update. To pin a specific
release, replace `main` with its full commit from the
[public history](https://github.com/FormalFrontier/algebraic-direct-limits).
Import the aggregate with `import AlgebraicDirectLimits`, or the linked leaf
appropriate to your use. No private research workspace is needed.

For a first use, follow
[`tensor_equiv_on_representatives`](tests/ReadinessClient.lean#L48) or
[`cofinal_restriction_without_nonempty`](tests/ReadinessClient.lean#L115).
The headline links also provide examples and boundary clients; client
namespaces are not public library declarations.

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
correspondences, if any, require separate assessment. The modules reuse native
constructions in [mathlib4](https://github.com/leanprover-community/mathlib4),
including `Mathlib.Algebra.Colimit.DirectLimit`,
`Mathlib.CategoryTheory.Filtered.Final`,
`Mathlib.CategoryTheory.CofilteredSystem`,
`Mathlib.Algebra.Category.Ring.FilteredColimits` and
`Mathlib.RingTheory.Localization.Pi`. References are mathematical background,
not quotations or claims of formalizing those exact texts.

Original Formal Frontier contributions credit Anchor (varying scalars,
cofinality and Mittag--Leffler systems), Prism (simple-ring colimits, graded
stabilization and monoidal research) and other Formal Frontier agents (including
the distinct Lean implementations for localization, cofinal completion and
monoidal completion). Anchor also contributed assembly and subsequent
improvements. See [contributors and provenance](docs/CREDITS.md) for details;
these are AI-assisted formal developments, not claims of source-author
endorsement. The finite-capture dimension bounds are Keel's formal development using
Mathlib's `Order.krullDim`, `LTSeries` and `PrimeSpectrum.comap`; the singleton
family recovers Mathlib's `ringKrullDim_le_of_surjective`. The directed-colimit
specialization and its models are also Keel's development, using Mathlib's
characteristic maps, representatives and directed finite-union capture API.
The directed-subsemiring union bound and its models use the same finite-capture
criterion, Mathlib's subsemiring union and inclusion API, and the integer and
rational dimension theorems.
The coinduced-module criterion follows Richard Hill and Andrew
Yang's Mathlib coinduced construction and `TopModuleCat.isColimit`
induced-topology proof. The same-topology restriction generalizes the restriction
object and continuous-map construction in Continuous Group Cohomology, including
Beacon's original development. Its algebraic objects and comparisons reuse
Jujian Zhang's Mathlib change-of-rings API; continuous maps reuse Sébastien Gouëzel
and Yury Kudryashov's restriction API. The regular-action continuity criterion
and Algebra agreement follow Mathlib's `continuous_algebraMap_iff_smul` and
`Algebra.smul_def`; the former is from the topological-algebra development by
Kim Morrison, Antoine Chambert-Loir and María Inés de Frutos-Fernández.
The one-sided tensor topology follows
scalar-extension ideas from
[Continuous Group Cohomology](https://github.com/FormalFrontier/continuous-group-cohomology)
by Formal Frontier Agents, including Beacon's original topological development.
Its local universe adapters reuse Mathlib's module and continuous-linear `ULift`
APIs directly. The continuous tensor universal property and scalar unit reuse
Kenny Lau and Mario Carneiro's Mathlib algebraic tensor lift, lift equivalence
and scalar unit; continuity is supplied by the fixed-coefficient generator
criterion. The modules name the contributors to their continuous-linear APIs.
The [Apache-2.0 license](LICENSE) covers original project material;
mathlib and the other separately maintained dependencies keep their own licenses
and notices. Collective author credit alone does not establish legal ownership
or resolve third-party rights concerns.
