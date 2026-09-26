# Mathematical guide

Import `AlgebraicDirectLimits` for the public aggregate, or one mathematical leaf
from the root README. All constructions use the pinned mathlib's native objects;
there is no alternative encoding of colimits, tensors, localizations or group
completions. Consult the Lean files for exact formal signatures and proofs.
The [generated API reference](API.md) supplies native displayed signatures and
relative source links; its [generation record](README.md) explains display limits.

## Varying scalar directed limits

Fix a nonempty directed preorder, a compatible directed system of commutative
semirings `A i`, and additive commutative monoids `M i` with `A i`-module structures.
The transition maps of the modules are semilinear along the scalar transition maps.
`DirectLimit.VaryingScalar.instModule` equips the concrete module limit with an
action of `ScalarLimit A f`. The scalar and module representatives may be moved
to a common larger stage to compute the action. Neither system needs injective
transition maps.

For two such module systems over the same scalar system, `tensorProductEquiv`
is a linear equivalence from the tensor product of their limits to the limit of
their stagewise tensor products. The forward map is induced by a balanced
bilinear pairing: move representatives to a common stage, then form their pure
tensor there. The reverse map sends a stage tensor to the tensor of its images.
The inverse laws reduce to common-stage representatives and tensor-product
induction. Index, scalar and both module types use independent universes.

Use `of`, `of_map`, `smul_mk` and the representative tensor rules in clients.
The named `toTensorLimit_tmul_mk` and `tensorProductEquiv_tmul_mk` work with explicit
`rw`. Ordinary `simp` uses the `..._tmul_mk_mk` quotient-normal-form rules after
`of_apply`; both paths are tested. This is a simplifier normal-form choice, not a
different comparison map or a restriction to constant scalars.

## Countable cofinality and inverse systems

`IsCofinal.exists_monotone_nat` starts with a countable cofinal subset of a nonempty
directed preorder. The entire index type need not be countable. A cofinal subset
is itself directed: first take an upper bound in the ambient preorder and then
move above it into the subset. Mathlib's sequentialization then supplies a
monotone cofinal map from the naturals and a corresponding final functor.

For Type-valued inverse systems, the Mittag--Leffler condition says that the
images in each fixed stage eventually stabilize. Restricting along a monotone
cofinal map preserves it; the restriction theorem does not assume the new index
type is nonempty. The nonempty-section theorem does require a nonempty directed
index with a countable cofinal subset and pointwise nonempty stage types. It
passes to a cofinal sequence, replaces each stage by its eventual range, and
uses the resulting surjective inverse sequence to construct a compatible section.

`evalSectionToEventualRange` records that every compatible section evaluates into
the eventual range. Surjectivity of this evaluation, under Mittag--Leffler and
the same index hypotheses, is proved by applying the nonempty-section theorem
to the system of preimages of a chosen eventual-range element. This surjectivity
theorem does not separately require all original stages to be nonempty.

## Simple rings and localization of products

`RingCat.FilteredColimits.colimit_isSimpleRing` treats a small filtered diagram
of simple rings. Transition maps are not assumed injective: simplicity of their
domains implies injectivity. Filtered-colimit equality then proves injectivity
of every stage map. A nonzero element of a nonzero ideal in the colimit comes
from some stage, where its ideal preimage contains1 by simplicity. Thus the
colimit ideal is top, and the colimit is nontrivial and simple.

`Localization.awayPiComparison r` maps localization of the countable product
at the constant tuple `r` to the product of the localizations away from `r`.
For a commutative domain, nonzero nonunit `r` makes this map non-surjective.
Every source fraction has one uniform denominator exponent `k`; the target
family with coordinate `r^(-n)` has no such bound. Evaluating a putative lift
at `k+1` would make `r` a unit. The theorem is about the literal countable product;
it does not assert failure for finite products, zero elements or units.

## Cofinal submonoids

For an additive commutative monoid `M`, a submonoid `L` with top saturation means
that every `m` has an ambient complement `c` with `m+c` in `L`. This is sufficient
for the canonical map to the Grothendieck additive group to be localization at
`L`. Consequently every group-completion element has a denominator in `L`, and
two canonical images agree exactly when their representatives agree after adding
one element of `L`. The map on group completions induced by inclusion of `L` is
injective. None of these conclusions requires cancellation in `M`.

## Monoidal object classes and actual image cofinality

`CategoryTheory.MonoidalGroupCompletion.objectClass X` is the class of an
object in the native `Additive (Skeleton C)`; its equality criterion is
isomorphism of objects. This needs only a category. The tensor/unit formulas
require a monoidal category but no braiding. For a strong monoidal functor
`F : C ⥤ D`, `skeletonMap F` is the native skeleton monoid hom in additive
notation; `imageSubmonoid F` is its *actual image* in the target skeleton.
`mem_imageSubmonoid_iff` recovers an actual source object from any image class.

When `D` is braided, `saturation_eq_top_iff F` identifies top saturation of
that image with the explicit condition that every target `Y` admits target
`Z` and source `X` with `Y ⊗ Z ≅ F.obj X`. No source braiding or full
faithfulness is required here, in `exists_object_denominator`, or in
`object_eq_iff_stabilizer`. These give actual image-object denominators and
identify equality of completed object classes by tensoring both representatives
with one `F.obj X`. No cancellation or essential surjectivity is assumed.

If both categories are braided, `completionMap F` is precisely the native
Grothendieck lift of `of.comp (skeletonMap F)`. Its generator law,
identity/composition laws for independent category universes, and invariance
under ordinary natural isomorphism are in the module. Full faithfulness yields
`imageEquiv F`, an additive equivalence onto the actual image, and the exact
homomorphism equation `completionMap_factorization F`. Together with cofinality
this proves `completionMap_injective F`; `completionRangeEquiv F` identifies the
source completion with the map's native subgroup *range*, not necessarily
the entire target group. See `tests/MonoidalGroupCompletionClient.lean` for
identity, equivalence, terminal, noncancellative and proper-image examples.

## Graded stabilization

Now take a degree homomorphism `d : M →+ A` and an element `u : M`. Stage `n` is
the fiber `d m = n • d u`; transition from `n` to `k` adds `(k-n) • u`.
Normalization sends a stage representative to `of m - n • of u` in the kernel
of the induced degree map. Transition compatibility is an additive calculation.
If multiples of `u` have top saturation, equality of normalizations is exactly
eventual equality after cyclic stabilization. This proves injectivity without
cancellation or injective transition maps.

Surjectivity additionally assumes cancellation in the degree target `A`, not
in `M`. A normalized expression for a kernel element then yields the required
degree-fiber equality. The resulting `normalizationEquiv` is an equivalence of
types. No additive structure on the fiber limit or additive equivalence is
claimed. Zero degree and an absorbing stabilizer are legitimate boundary cases,
illustrated by the checked clients. The generic computations preserve independent
universes for `M` and `A`.

These results are reusable mathematical statements. This guide and the metadata
do not assert completeness of a mathematical source or a source-specific theorem.
