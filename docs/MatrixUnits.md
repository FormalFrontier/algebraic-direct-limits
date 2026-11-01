# Finite matrix units and directed limits

Taking units of finite square matrices commutes with directed limits of
semirings. The comparison sends a stage unit to its entrywise image; its
inverse is described by descending both a matrix and its stored inverse.
Equality is detected at a common later stage, not necessarily at either
original stage.

The declarations are in [Matrix.Units](../AlgebraicDirectLimits/Matrix/Units.lean).
Use `import AlgebraicDirectLimits.Matrix.Units`; names below are in the
`DirectLimit` namespace. Here "matrix units" means invertible matrices,
that is, elements of `(Matrix κ κ R)ˣ`, not the elementary matrices.

## Hypotheses and carriers

Let `ι : Type uι` be a nonempty directed preorder, with instances
`[Preorder ι] [IsDirectedOrder ι] [Nonempty ι]`. Supply
`R : ι → Type uR` with `[∀ i, Semiring (R i)]` and bundled ring homomorphisms

```text
f : ∀ i j, i ≤ j → R i →+* R j
```

Assume `[DirectedSystem R (fun i j h ↦ (f i j h : R i → R j))]`.
The supplied dimension `κ : Type uκ` has `[Fintype κ] [DecidableEq κ]`.
The universes `uι`, `uR` and `uκ` are independent. Coefficients need not
commute, transitions need not be injective, and no `Nontrivial` assumption
is imposed. The dimension `κ` may be empty.

Write `L = _root_.DirectLimit R f`, `cᵢ = DirectLimit.Ring.of R f i`,
and `U i = (Matrix κ κ (R i))ˣ`. Set

```text
τ i j h = DirectLimit.matrixUnitsMap κ R f i j h
        = Units.map (f i j h).mapMatrix.toMonoidHom
```

`matrixUnitsDirectedSystem` supplies the directed-system laws for `U, τ`.
The source uses the existing direct-limit quotient and group operations.

## The canonical comparison

The multiplicative equivalence is

```text
DirectLimit.matrixUnitsColimitEquiv κ R f :
  _root_.DirectLimit U τ ≃* (Matrix κ κ L)ˣ
```

Its forward monoid homomorphism is `matrixUnitsToLimit κ R f`. The stage
monoid homomorphism `matrixUnitsOf κ R f i` is
`Units.map (DirectLimit.Ring.of R f i).mapMatrix.toMonoidHom`.

For `u : U i`, write `u.val` for its value matrix and `u.inv` for its
stored two-sided inverse. For entries `a b : κ`, the transition formulas
are

```text
(τ i j h u).val a b = f i j h (u.val a b)
(τ i j h u).inv a b = f i j h (u.inv a b)
```

These are `matrixUnitsMap_val_apply` and `matrixUnitsMap_inv_apply`.

The corresponding stage-to-limit formulas are

```text
(matrixUnitsOf κ R f i u).val a b = cᵢ (u.val a b)
(matrixUnitsOf κ R f i u).inv a b = cᵢ (u.inv a b)
```

They are `matrixUnitsOf_val_apply` and `matrixUnitsOf_inv_apply`.
The inverse formula concerns the inverse stored in a unit, not a separately
defined inverse operation on arbitrary matrices.

Compatibility is expressed by `matrixUnitsOf_f`:

```text
matrixUnitsOf κ R f j (τ i j h u) = matrixUnitsOf κ R f i u
```

Thus the forward map on a quotient representative is

```text
matrixUnitsToLimit κ R f ⟦⟨i, u⟩⟧ = matrixUnitsOf κ R f i u
matrixUnitsColimitEquiv κ R f ⟦⟨i, u⟩⟧ = matrixUnitsOf κ R f i u
```

The lemmas are `matrixUnitsToLimit_mk` and `matrixUnitsColimitEquiv_mk`.
The reverse direction on a stage image is
`matrixUnitsColimitEquiv_symm_apply_stage`:

```text
(matrixUnitsColimitEquiv κ R f).symm (matrixUnitsOf κ R f i u) = ⟦⟨i, u⟩⟧
```

The equivalence is noncomputable. Choosing representatives describes its
inverse; the forward map is fixed by the canonical stage maps.

## Representation and exact eventual equality

`exists_matrix_unit_representation κ R f w` says that every
`w : (Matrix κ κ L)ˣ` admits an index `i` and `u : U i` with
`matrixUnitsOf κ R f i u = w`. This is descent as a *unit*: the stage
matrix has a two-sided inverse at that same stage, not just an inverse
after applying `cᵢ`.

For `u : U i` and `v : U j`, `matrixUnitsOf_eq_iff κ R f u v` gives
exactly

```text
matrixUnitsOf κ R f i u = matrixUnitsOf κ R f j v ↔
  ∃ (k : ι) (hik : i ≤ k) (hjk : j ≤ k),
    matrixUnitsMap κ R f i k hik u = matrixUnitsMap κ R f j k hjk v
```

Both source bounds are part of the witness. The conclusion is equality
of transported units at one common stage.

In particular, even if `i = j`, equality of limit images need not mean
equality at stage `i`: a noninjective transition can identify distinct
values. Conversely, equality at a later stage gives equality in the limit
by compatibility. The statements `matrixUnitsToLimit_injective` and
`matrixUnitsToLimit_surjective` package these facts into bijectivity of
the comparison.

## Why finite capture suffices

For surjectivity, jointly capture the finitely many entries of the value
matrix `w.val` and inverse matrix `w.inv` at one stage. This produces
matrices `A₀, B₀` whose images are the two matrices in the limit. It does
not yet imply `A₀ * B₀ = 1` or `B₀ * A₀ = 1` at that stage.

Reflect the finitely many entry equalities in **both** ordered equations
`w.val * w.inv = 1` and `w.inv * w.val = 1`. Refine their witnesses to a
common stage, transporting `A₀, B₀` together. There the two equations
hold as `A * B = 1` and `B * A = 1`, so `A, B` package into a stage
unit. Neither equation can be discarded for arbitrary semirings.

For injectivity, equality of stage images implies equality of every
value entry in the coefficient limit. Finite equality reflection gives
one common stage above both sources where all those entries agree.
`Units.ext` turns equality of value matrices into equality of units; a
second reflection argument for inverse entries is unnecessary.

If `κ` is empty there are no entries to capture or compare, but there
must still be a stage representing a unit. This is why the nonempty
index hypothesis remains. Equality reflection must also retain the
bounds above both supplied stages even for an empty family. No
nonempty-dimension hypothesis is needed.

## Simultaneous product descent

The underlying tool is `DirectLimit.exists_matrix_products` in
[ProductDescentSignature](../AlgebraicDirectLimits/Matrix/ProductDescentSignature.lean).
It works over the weaker floor `[∀ i, NonUnitalNonAssocSemiring (R i)]`,
for an implicit function-like family `F` with `NonUnitalRingHomClass`
instances and an independent universe `uF`:

```text
F : ∀ ⦃i j : ι⦄, i ≤ j → Type uF
f : ∀ i j (h : i ≤ j), F h
```

For each `i j h` the assumptions are `FunLike (F h) (R i) (R j)` and
`NonUnitalRingHomClass (F h) (R i) (R j)`, together with the directed-system
laws for the underlying functions. The explicit initial arguments remain
`exists_matrix_products R f`.

For finite dimensions `κ, ν` in independent universes, take rectangular
limit matrices `X : Matrix κ ν (DirectLimit R f)` and
`Y : Matrix ν κ (DirectLimit R f)`. Given stage matrices
`P : Matrix κ κ (R i)` and `Q : Matrix ν ν (R j)` such that
`X * Y` is the image of `P` and `Y * X` is the image of `Q`, the theorem
produces one `k` above `i` and `j` and matrices `A, B` at `k` with

```text
A.map (DirectLimit.NonUnitalRing.of R f k) = X
B.map (DirectLimit.NonUnitalRing.of R f k) = Y
A * B = P.map (f i k hik)
B * A = Q.map (f j k hjk)
```

Here `hik : i ≤ k` and `hjk : j ≤ k`. Both dimensions may be empty;
neither associativity, a multiplicative identity nor injectivity of the
transitions is needed for this product-descent statement.

For matrix units, specialize to square matrices over semirings, set
`X = w.val`, `Y = w.inv`, and choose identity matrices for `P, Q` at an
index supplied by `Nonempty ι`. Mapping these identities gives identities,
so the two descended product equations supply the unit laws.

The units construction passes the original bundled ring-hom family `f`
to this same product theorem. There is no need to replace `f` by another
family of nonunital bundles. Keeping `R`, `f` and their chosen algebraic
instances fixed keeps the coefficient quotient `DirectLimit R f` fixed,
avoiding transports between quotient carriers or algebraic dictionaries.

This is a specialization of one product-descent API, not a second engine
or an override of the semiring instances. The comparison concerns finite
square matrices; it asserts no analogous infinite-matrix surjectivity.

The construction uses Mathlib's direct limits, matrix maps and units.
See the [project credits and license](../README.md#credits-and-license).
