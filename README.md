# Algebraic Direct Limits

This library works with Mathlib's directed limits, localizations,
Grothendieck group completions and categorical colimits, and with one-sided
topological tensor products. Import `AlgebraicDirectLimits` for the core APIs,
or use the individual modules linked below. The rational-circle modules are
separate imports.

The [guide](GUIDE.md) contains the detailed mathematics, supporting APIs,
examples and [full module catalogue](GUIDE.md#modules).

## Headline results

- **Semilinear quotient descent.** A continuous semilinear map from a module
  over a ring to a module over a semiring descends through any submodule in
  its kernel, retaining the original module structures and quotient topology.
  The codomain need only be an additive commutative monoid; continuity of
  module operations is not assumed. See
  [Quotient](AlgebraicDirectLimits/Topology/Module/Quotient.lean).
- **Varying scalars and tensor products.** For compatible semilinear module
  systems over a nonempty directed preorder, the tensor product of the two
  module limits over the varying commutative-semiring limit is equivalent to
  the limit of the stagewise tensor products. Transition maps need not be
  injective. See [VaryingScalar](AlgebraicDirectLimits/VaryingScalar.lean).
- **Mittag--Leffler inverse systems.** A pointwise nonempty, Type-valued
  Mittag--Leffler inverse system over a nonempty directed preorder with a
  countable cofinal subset has a compatible section. Under the same index and
  Mittag--Leffler conditions, each element of an eventual range lifts to a
  section without a separate pointwise-nonemptiness assumption. See
  [MittagLeffler](AlgebraicDirectLimits/MittagLeffler.lean).
- **Prime spectra of filtered colimits.** For a small filtered category and
  any colimit cocone of commutative rings, its spectrum cone is a limit in
  topological spaces. The chosen-limit homeomorphism identifies coordinates
  with contraction along the cocone maps; no injectivity or nonzero-ring
  assumption is required. See
  [PrimeSpectrumFilteredColimits](AlgebraicDirectLimits/PrimeSpectrumFilteredColimits.lean).
- **Krull dimension under finite-subset capture.** For homomorphisms
  `φ i : A i →+* B` of commutative semirings, if every finite subset of `B`
  lies in the range of one `φ i`, then
  `ringKrullDim B ≤ ⨆ i, ringKrullDim (A i)`. The family need not be directed
  and the maps need not be injective; dimensions include `⊥` and `⊤`. See
  [FiniteCapture](AlgebraicDirectLimits/RingTheory/KrullDimension/FiniteCapture.lean).
- **Module topology on finite-dimensional strong duals.** Over any normed
  field, the continuous dual of a finite-dimensional topological vector space
  with module topology also has module topology, retaining its topology of
  uniform convergence on bounded sets. Neither completeness nor a nontrivial
  norm on the field is required. This is an explicit theorem, not a global
  instance. See [StrongDual](AlgebraicDirectLimits/Topology/StrongDual.lean).
- **Flat-coefficient tensor monomorphisms.** Over a commutative ring with a
  supplied topology, tensoring the topological module factor with a flat
  algebraic coefficient module preserves injectivity of continuous linear
  maps and categorical monomorphisms. No coefficient topology is required.
  See [TensorFunctor](AlgebraicDirectLimits/Topology/TensorFunctor.lean).
- **Coefficient tensor–continuous Hom adjunction.** For a commutative ring
  with a supplied topology and a topological module with jointly continuous
  scalar action, coefficient tensor is left adjoint to the algebraic
  continuous-Hom functor, in a common carrier universe independent of the
  scalar universe. It preserves existing colimits of arbitrary diagram size;
  neither coefficients nor the Hom module are given a topology. See
  [CoefficientTensor](AlgebraicDirectLimits/Topology/CoefficientTensor.lean).
- **Continuous tensor quotients.** For a commutative ring `R` with a supplied
  topology, an algebraic coefficient module `C`, a topological module `M` with
  jointly continuous scalar action and any submodule `P`, there is a continuous
  linear equivalence `C ⊗[R] (M ⧸ P) ≃L[R] (C ⊗[R] M) ⧸ K`, where
  `K = LinearMap.range (TensorProduct.map LinearMap.id P.subtype)`.
  This is the range, not its closure; no flatness or closedness assumption is
  required. See [Quotient](AlgebraicDirectLimits/Topology/TensorProduct/Quotient.lean).
- **Projective coefficients preserve tensor Hausdorffness.** Over a
  commutative ring with a supplied topology, the one-sided tensor of a
  projective algebraic coefficient module with a Hausdorff topological module
  with jointly continuous scalar action is Hausdorff. No coefficient topology
  or finiteness assumption is required. See
  [TensorSeparation](AlgebraicDirectLimits/Topology/TensorSeparation.lean).
- **Flat coefficients need not preserve tensor Hausdorffness.** The one-sided
  tensor `ℚ ⊗[ℤ] AddCircle (1 : ℝ)` is not Hausdorff, although the rational
  coefficient module is flat and the usual real circle is compact Hausdorff
  with jointly continuous integer action. See the
  [rational-circle counterexample](AlgebraicDirectLimitsExamples/TensorCircleClient.lean).

For further results and characteristic formulas, see the
[guide's headline results](GUIDE.md#headline-results) and the
[coefficient tensor–Hom naturality guide](docs/coefficient-tensor-hom-naturality.md).

## Using the library

With a matching Lean toolchain, add this dependency to your `lakefile.toml`:

```toml
[[require]]
name = "algebraic-direct-limits"
git = "https://github.com/FormalFrontier/algebraic-direct-limits.git"
rev = "main"
```

GitHub `main` contains reviewed releases. Lake resolves the latest release when
you first add or update the dependency; `lake-manifest.json` retains that commit
until the next update. To pin a specific release, replace `main` with its full
commit from the [public history](https://github.com/FormalFrontier/algebraic-direct-limits).

```lean
import AlgebraicDirectLimits
```

For a first use, follow the
[tensor equivalence on representatives](tests/ReadinessClient.lean#L54) or
[cofinal restriction](tests/ReadinessClient.lean#L121) clients. Client namespaces
are not public library declarations. Mathlib is the sole direct dependency;
when combining Lean libraries, use releases built against a common Mathlib
revision and one revision of this package.

## Building and API limits

The toolchain and dependencies are pinned in the repository. With the matching
Lean toolchain installed, fetch the matching Mathlib cache before building:

```sh
lake exe cache get
lake --wfail build
```

Arbitrary product coordinates detect equality but do not give an
infinite-product inverse or surjectivity. Projective Hausdorff preservation
does not imply reflection or finite generation; tensor compactness preservation
assumes finitely generated coefficients and a compact right factor. Completed
tensor products and full categorical tensor coherence are outside this API.
See the [usage limitations](GUIDE.md#using-the-library) and
[reproduction instructions](GUIDE.md#reproduce) for details.

## Credits and license

Authors: Formal Frontier Agents. These are AI-assisted formal developments
reusing [Mathlib](https://github.com/leanprover-community/mathlib4).
The Stacks Project provides mathematical background on
[Mittag--Leffler inverse limits](https://stacks.math.columbia.edu/tag/0597) and
[filtered colimits](https://stacks.math.columbia.edu/tag/07N7), not a claim of
formalizing those exact texts or of source-author endorsement. See the
[full references and credits](GUIDE.md#references-and-credits) and
[contributors and provenance](docs/CREDITS.md) for attribution details.
Licensed under [Apache-2.0](LICENSE).
