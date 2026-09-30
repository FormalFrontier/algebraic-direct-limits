# Algebraic Direct Limits

Authors: Formal Frontier Agents. License: [Apache-2.0](LICENSE).

This library works with mathlib's native directed limits, localizations,
Grothendieck group completions and categorical colimits. Import the
[public aggregate](AlgebraicDirectLimits.lean) with `import AlgebraicDirectLimits`,
or import any of the eight mathematical modules individually.

## Headline results

- **Varying scalars and tensor products.**
  [`DirectLimit.VaryingScalar.tensorProductEquiv`](AlgebraicDirectLimits/VaryingScalar.lean#L429)
  identifies the tensor product of two module limits over a *varying*
  commutative-semiring limit with the limit of their stagewise tensor products.
  It uses compatible semilinear module systems over a nonempty directed preorder,
  with four independent universes and no injectivity assumption on transitions.
  See the [module](AlgebraicDirectLimits/VaryingScalar.lean) and
  [representative client](tests/ReadinessClient.lean#L48).
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

The [mathematical guide](docs/Guide.md) explains the constructions and proofs;
the Lean modules give the exact signatures and hypotheses. The
[historical API display](docs/API.md) selects **73 library and 23 boundary-client
sites from seven earlier leaves** at its recorded source revision. Its inputs
are source-byte equivalent to the [initial published library snapshot](https://github.com/FormalFrontier/algebraic-direct-limits/tree/d3e1787bbc962d028698af2259d2ef31212857d1),
but this does not mean its native displays were generated at that public commit.
It does not cover `MonoidalGroupCompletion`, the current aggregate/test roots or
all private/generated declarations. Use the module source and guide for omitted
material; client namespaces are not re-exported as library APIs. This library
does not claim a complete theory of limits or formal coverage of a specific
mathematical source.

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

The default targets in [`lakefile.toml`](lakefile.toml) are the aggregate and
[`ReadinessTests`](tests/ReadinessTests.lean), which imports four clients (three
boundary clients and the aggregate-import client). To check a narrow module or
client after the cache succeeds, for example:

```sh
lake --wfail build AlgebraicDirectLimits.MonoidalGroupCompletion
lake env lean -DwarningAsError=true tests/ReadinessClient.lean
```

External projects should use a matching Lean toolchain and pin their Lake Git
dependency to a **full published release commit** of
[FormalFrontier/algebraic-direct-limits](https://github.com/FormalFrontier/algebraic-direct-limits),
not a moving branch or development commit. No private research workspace is
needed. Import the aggregate or the linked leaf module appropriate to the use.

For a first use, follow
[`tensor_equiv_on_representatives`](tests/ReadinessClient.lean#L48) or
[`cofinal_restriction_without_nonempty`](tests/ReadinessClient.lean#L115).
The [graded client](tests/GradedStabilizationClient.lean) covers zero degree,
noninjective transitions and noncancellative source monoids; the
[cofinal-completion client](tests/CofinalGroupCompletionClient.lean) covers a
proper cofinal submonoid. The
[monoidal client](tests/MonoidalGroupCompletionClient.lean) checks the actual
image, range equivalence and a fully faithful doubling example that is not
essentially surjective. These checked examples are not public library declarations.

## Historical resource observation

On an *earlier seven-leaf configuration*, a fresh matching mathlib-cache fetch
took about 86 seconds for 8,892 artifacts. With that cache retained, eleven
sequential explicit library/client builds, a 2,256-job default build and three
diagnostic commands took about 44 seconds in total. These are measured times on
one Linux x86-64 runtime with a 23 GiB shared cgroup limit, **not** current
eight-leaf timings, clean dependency-source builds or machine-independent
benchmarks. That configuration's explicit test-library globs omitted the
`ReadinessTests` re-export now present in the default targets. Sampled total
cgroup memory stayed below 20 GB but included another retained cache and file
cache; it was not a compiler peak. No full-current measurement or validated
smaller-machine memory estimate is available. As unvalidated planning advice,
allow headroom for the matching cache and concurrently scheduled Lean jobs;
prefer checking one target at a time when constrained. Do not replace a failed
cache fetch with a full mathlib source build.

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
endorsement. The [Apache-2.0 license](LICENSE) covers original project material;
mathlib and the other separately maintained dependencies keep their own licenses
and notices. Collective author credit alone does not establish legal ownership
or resolve third-party rights concerns.
