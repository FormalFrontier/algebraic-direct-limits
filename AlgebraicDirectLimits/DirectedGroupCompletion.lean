/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AlgebraicDirectLimits.CofinalGroupCompletion
public import Mathlib.Order.DirectedInverseSystem
public import Mathlib.Order.Directed
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup

/-!
# Directed families and Grothendieck additive groups

A coherent, jointly surjective family of additive maps to a commutative monoid
induces a jointly surjective family on Grothendieck additive groups. This only
requires a common upper stage for each pair of stages, not the identity or
composition laws for the transition maps.

For a directed system, suppose also that equality of cocone images is witnessed
at a common stage. Equality of the induced images in the target Grothendieck
additive group is then equivalent to equality at a common completed stage.
The maps throughout are `lift ((of (M := B)).comp (c i))` and the corresponding
lifts of the given transition maps.

No cancellation in the monoids or injectivity of their canonical maps to group
completion is required. In particular, completed equality is not replaced by
unstabilized equality of monoid representatives. The difference representatives
and stable-equality criterion are supplied by
`exists_cofinal_denominator` and `of_eq_iff_exists_cofinal_stabilizer` at the top
submonoid. Joint surjectivity already implies that the index is nonempty by
representing zero, so no separate nonemptiness assumption is needed.

## References

* Alex J. Best and Yaël Dillies, Mathlib's
  `Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup`, for the
  Grothendieck additive group and its `lift` equivalence.
* `AlgebraicDirectLimits.CofinalGroupCompletion`, for difference representatives
  and equality after adding a common stabilizer.
* Junyan Xu, Mathlib's `Mathlib.Order.DirectedInverseSystem`, for the
  `DirectedSystem` interface.
-/

@[expose] public section

universe uι uA uB

namespace Algebra.GrothendieckAddGroup

private theorem lift_comp_of_apply
    {M : Type uA} {N : Type uB} [AddCommMonoid M] [AddCommMonoid N]
    (g : M →+ N) (a : M) :
    lift ((of (M := N)).comp g) (of a) = of (g a) :=
  DFunLike.congr_fun
    ((lift (M := M) (G := GrothendieckAddGroup N)).symm_apply_apply
      ((of (M := N)).comp g)) a

/-- A coherent, jointly surjective family of additive maps induces a jointly
surjective family on Grothendieck additive groups. Only binary directedness of
the index relation is needed; the transition maps need not satisfy identity or
composition laws. -/
theorem jointly_surjective_lift_of_jointly_surjective
    {ι : Type uι} [LE ι] [IsDirectedOrder ι]
    {A : ι → Type uA} [∀ i, AddCommMonoid (A i)]
    {B : Type uB} [AddCommMonoid B]
    (f : ∀ i j : ι, i ≤ j → A i →+ A j)
    (c : ∀ i : ι, A i →+ B)
    (hc : ∀ (i j : ι) (h : i ≤ j), (c j).comp (f i j h) = c i)
    (hs : ∀ b : B, ∃ (i : ι) (a : A i), c i a = b)
    (z : GrothendieckAddGroup B) :
    ∃ (i : ι) (x : GrothendieckAddGroup (A i)),
      lift ((of (M := B)).comp (c i)) x = z := by
  obtain ⟨a, b, hz⟩ := exists_cofinal_denominator (⊤ : AddSubmonoid B) (by simp) z
  obtain ⟨i, x, hx⟩ := hs a
  obtain ⟨j, y, hy⟩ := hs (b : B)
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
  refine ⟨k, of (f i k hik x) - of (f j k hjk y), ?_⟩
  have hix : c k (f i k hik x) = a := (DFunLike.congr_fun (hc i k hik) x).trans hx
  have hjy : c k (f j k hjk y) = (b : B) :=
    (DFunLike.congr_fun (hc j k hjk) y).trans hy
  simpa only [map_sub, lift_comp_of_apply, hix, hjy] using hz.symm

/-- For a directed system with a coherent, jointly surjective cocone that
reflects equality at a common stage, two images in the target Grothendieck
additive group agree if and only if their images agree in a common stage's
Grothendieck additive group. No cancellation or injectivity is assumed for the
monoids or the cocone maps. -/
theorem lift_eq_lift_iff_exists
    {ι : Type uι} [Preorder ι] [IsDirectedOrder ι]
    {A : ι → Type uA} [∀ i, AddCommMonoid (A i)]
    {B : Type uB} [AddCommMonoid B]
    (f : ∀ i j : ι, i ≤ j → A i →+ A j)
    [DirectedSystem A
      (fun ⦃i j⦄ (h : i ≤ j) => (f i j h : A i → A j))]
    (c : ∀ i : ι, A i →+ B)
    (hc : ∀ (i j : ι) (h : i ≤ j), (c j).comp (f i j h) = c i)
    (hs : ∀ b : B, ∃ (i : ι) (a : A i), c i a = b)
    (he : ∀ (i j : ι) (a : A i) (b : A j), c i a = c j b →
      ∃ (k : ι) (hik : i ≤ k) (hjk : j ≤ k),
        f i k hik a = f j k hjk b)
    (i j : ι) (x : GrothendieckAddGroup (A i))
    (y : GrothendieckAddGroup (A j)) :
    lift ((of (M := B)).comp (c i)) x =
        lift ((of (M := B)).comp (c j)) y ↔
      ∃ (k : ι) (hik : i ≤ k) (hjk : j ≤ k),
        lift ((of (M := A k)).comp (f i k hik)) x =
          lift ((of (M := A k)).comp (f j k hjk)) y := by
  have hc_apply (l m : ι) (h : l ≤ m) (a : A l) :
      c m (f l m h a) = c l a :=
    DFunLike.congr_fun (hc l m h) a
  obtain ⟨a, b, rfl⟩ :=
    exists_cofinal_denominator (⊤ : AddSubmonoid (A i)) (by simp) x
  obtain ⟨d, e, rfl⟩ :=
    exists_cofinal_denominator (⊤ : AddSubmonoid (A j)) (by simp) y
  simp only [map_sub, lift_comp_of_apply]
  constructor
  · intro h
    have hsum : of (c i a + c j (e : A j)) = of (c j d + c i (b : A i)) := by
      simpa only [map_add] using sub_eq_sub_iff_add_eq_add.mp h
    obtain ⟨t, ht⟩ :=
      (of_eq_iff_exists_cofinal_stabilizer (⊤ : AddSubmonoid B) (by simp)
        (c i a + c j (e : A j)) (c j d + c i (b : A i))).mp hsum
    obtain ⟨p, s, hst⟩ := hs (t : B)
    obtain ⟨r, hir, hjr, hpr⟩ := directed_of₃ (· ≤ ·) i j p
    let u : A r := f i r hir a + f j r hjr (e : A j) + f p r hpr s
    let v : A r := f j r hjr d + f i r hir (b : A i) + f p r hpr s
    have huv : c r u = c r v := by
      simpa only [u, v, map_add, hc_apply, hst] using ht
    obtain ⟨k, hrk, _, hk⟩ := he r r u v huv
    refine ⟨k, hir.trans hrk, hjr.trans hrk, ?_⟩
    have hstable :
        f i k (hir.trans hrk) a + f j k (hjr.trans hrk) (e : A j) +
            f p k (hpr.trans hrk) s =
          f j k (hjr.trans hrk) d + f i k (hir.trans hrk) (b : A i) +
            f p k (hpr.trans hrk) s := by
      simpa only [u, v, map_add, DirectedSystem.map_map' f] using hk
    have hcompleted := congrArg (of (M := A k)) hstable
    simp only [map_add] at hcompleted
    -- The common stabilizer can be cancelled in the completed group, not in `A k`.
    exact sub_eq_sub_iff_add_eq_add.mpr (add_right_cancel hcompleted)
  · rintro ⟨k, hik, hjk, h⟩
    have hcompleted := congrArg (lift ((of (M := B)).comp (c k))) h
    simpa only [map_sub, lift_comp_of_apply, hc_apply] using hcompleted

end Algebra.GrothendieckAddGroup
