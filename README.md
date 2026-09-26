# Algebraic Direct Limits

Authors: Formal Frontier Agents. License: [Apache-2.0](LICENSE).

This Lean library supplies eight independently importable modules, also available
through the public aggregate `import AlgebraicDirectLimits`:

| Module | Reusable results and boundaries |
| --- | --- |
| `AlgebraicDirectLimits.VaryingScalar` | Semilinear directed limits and a tensor-product linear equivalence for four independent universes; no injectivity of transition maps. |
| `AlgebraicDirectLimits.CofinalSequence` | Monotone cofinal sequence and final functor from a countable cofinal subset of a nonempty directed preorder; the preorder need not be countable. |
| `AlgebraicDirectLimits.MittagLeffler` | Sections of pointwise nonempty Type-valued Mittag--Leffler inverse systems and surjective evaluation onto eventual ranges over such directed preorders. |
| `AlgebraicDirectLimits.SimpleRing` | Simplicity of filtered colimits of simple rings in `RingCat`; injectivity is derived, not assumed. |
| `AlgebraicDirectLimits.LocalizationPi` | Comparison for localization of a countable product at a constant element; non-surjectivity for a nonzero nonunit in a commutative domain. |
| `AlgebraicDirectLimits.CofinalGroupCompletion` | Localization and stabilization for a top-saturated submonoid of any additive commutative monoid; no cancellation assumption. |
| `AlgebraicDirectLimits.MonoidalGroupCompletion` | Actual image of a strong monoidal functor on additive skeleta; object cofinality gives image denominators/stabilization, and full faithfulness gives injectivity of its native completion map. |
| `AlgebraicDirectLimits.GradedStabilization` | Native degree-fiber direct limits and normalization into a group-completion kernel; injectivity needs top saturation, while surjectivity/type equivalence also needs cancellation of the degree target only. |

The graded equivalence is an equivalence **of types**, not an additive
equivalence. The library does not claim a complete theory of algebraic limits,
complete formalization of any source, or coverage of unproved statements.
Source-specific passage correspondence and coverage belong in separate source
repositories; this library is usable without them.

Start with the [mathematical guide](docs/Guide.md) and the
[checked clients](tests/ReadinessClient.lean), including the
[monoidal completion client](tests/MonoidalGroupCompletionClient.lean).
The [historical generated API reference](docs/API.md) records 73 library and
23 boundary-client native display sites for the earlier seven-module input at
its recorded revision; it does **not** cover the new eighth module or changed
root/tests. The new API is documented in the
[new module](AlgebraicDirectLimits/MonoidalGroupCompletion.lean) and mathematical
guide. The historical display inventory is not a private/generated proof census. Boundary-test
namespaces are not re-exported by the library root and are not additional
advertised library APIs.

## Reproduce

The repository pins Lean `leanprover/lean4:v4.34.0-rc2` in `lean-toolchain` and
mathlib `83abb3e776bdefcbc447a1e44d0debe4010039e5` in both `lakefile.toml`
and `lake-manifest.json`. Mathlib is the sole direct dependency. The manifest
also fixes eight transitive packages (`plausible`, `LeanSearchClient`,
`importGraph`, `proofwidgets`, `aesop`, `Qq`, `batteries`, `Cli`). Install the
pinned toolchain with `elan`, and allow network access to retrieve dependencies
and the matching precompiled mathlib cache. The intended distribution repository
is [FormalFrontier/algebraic-direct-limits](https://github.com/FormalFrontier/algebraic-direct-limits).
Access to a private distribution requires authorized GitHub access. This URL
alone does not establish publication or acceptance of a particular release.
The source tree itself has no dependency on a private research workspace.
From the repository root:

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
lake exe cache get
lake --wfail build
lake --wfail build ReadinessTests
lake --wfail build AlgebraicDirectLimits.MonoidalGroupCompletion
lake env lean -DwarningAsError=true tests/MonoidalGroupCompletionClient.lean
lake env lean -DwarningAsError=true tests/ReadinessClient.lean
```

The default build includes the public aggregate and the separate
`ReadinessTests` target; that target imports all three boundary clients and
the root-import client. Individual source files are also checkable with the
same `lake env lean` commands. `-T0` disables the allocation timeout; it is
not a change of trust level or an independent proof replay. Client namespaces
and private test declarations are checks, not advertised public library APIs.
An outside project can import `AlgebraicDirectLimits` using a matching Lean
toolchain and a Lake dependency on this repository; importing individual modules
is supported too.

For a first use, follow `tensor_equiv_on_representatives` or
`cofinal_restriction_without_nonempty` in `tests/ReadinessClient.lean`.
Both are stable named, build-checked private examples with just the public
aggregate import. `tests/GradedStabilizationClient.lean` additionally demonstrates
zero degree, noninjective transitions and noncancellative source monoids; the
cofinal-completion client includes a proper cofinal submonoid and noncancellative
boundary cases. These are mathematical examples, not tests that add assumptions
to the public declarations.
`tests/MonoidalGroupCompletionClient.lean` also exercises weak-hypothesis
object classes, functoriality, exact image factorization, a subgroup-range
equivalence and the noncancellative/doubling boundary cases.

## Initial resource baseline

On the earlier `7d61d5d` Lean4.34.0-rc2 candidate, a fresh matching cache fetch took about
86 seconds and supplied8892 mathlib cache artifacts. With that cache retained,
the eleven sequential explicit library/client builds plus the actual2256-job
default build and three diagnostic commands completed in about44 seconds.
This is a warm-dependency owner measurement on a Linux x86-64 agent runtime with
a23GiB shared cgroup limit, not a clean dependency-source rebuild or a hardware-
independent benchmark. Sampled total cgroup memory stayed below20GB and included
another retained cache and file cache; it is not the compiler's private peak.
No speedup over a former release is claimed. The historical stored-proof audit
was a separate diagnostic, not a required repeat gate for new contributions;
build and complete transitive standard-axiom checks are the computational checks.
Exact commands and
resource samples accompany that candidate's evidence. Its explicit test-library
globs omitted the separate shipped `ReadinessTests` re-export. The configuration adds
that module to the globs; the earlier timings are not a measurement of this
configuration or a claim that the omitted module was checked by those commands.

## Mathematical and formal credits

The [Stacks Project, Algebra, Lemma 10.86.3](https://stacks.math.columbia.edu/tag/0597)
is a mathematical reference for nonempty Mittag--Leffler inverse limits over
countable indices. The present countable-*cofinal*-subset theorem has a different
index hypothesis and is not a claim of verbatim translation or source coverage.
The [Stacks Project, Algebra, Section 10.8](https://stacks.math.columbia.edu/tag/07N7)
provides mathematical background on filtered colimits; specific source
correspondences, if any, require separate assessment. Mathematical foundations
already formalized in the pinned mathlib are reused, notably
`Mathlib.Algebra.Colimit.DirectLimit`,
`Mathlib.CategoryTheory.Filtered.Final`,
`Mathlib.CategoryTheory.CofilteredSystem`,
`Mathlib.Algebra.Category.Ring.FilteredColimits` and
`Mathlib.RingTheory.Localization.Pi`. Consult the leaf module headers for
their exact assumptions and definitions. References credit mathematical ideas;
no excerpts or original source assets are reproduced here.

Original project contributions list **Formal Frontier Agents** as authors.
The historical mathematical leaves were contributed by Anchor (varying scalars,
cofinal sequences and Mittag--Leffler systems), Prism (simple-ring colimits and
graded stabilization), a worker-a Task (localization of countable products), and
a worker-b Task (cofinal group completion). Their exact reviewed commits and
Task attributions are preserved in the shipped [contributor/provenance record](docs/CREDITS.md).
Prior formal
developments and this worker-b assembly involve AI-assisted agent work;
the checked Lean files, not model output alone, are the mathematical artifact.
The readiness assembly was contributed by a worker-b Task; Anchor made the
provenance-backed header correction and the computation-rule/client repairs.
The bundled `LICENSE`
is Apache-2.0. Original project files use SPDX license identifiers and collective
author credit; unsupported project-generated copyright-owner labels were removed
after checking their first-added history. No replacement holder is inferred.
Mathlib and other downloaded dependencies retain their own licenses and
attribution. Standing project authorization covers verified original Formal
Frontier contributions, but collective author credit does not establish legal
ownership or clear third-party rights. Exact provenance, real contributor credit,
and concrete third-party licensing concerns still require independent review.

An ordinary build, metadata or generated reference alone is not release
acceptance or copyright clearance. Each exact release requires applicable
independent public-API semantic review, a complete shipped-declaration axiom
census, documentation and provenance/rights review, followed by protected
promotion and a separate publication decision.
Historical development records do not approve later artifacts or source coverage.
