/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Colimit.DirectLimit
public import Mathlib.Data.Matrix.Mul
import AlgebraicDirectLimits.Order.DirectedSystem

/-!
# Simultaneous rectangular products

Rectangular factors in a directed limit descend together with two prescribed products,
even when those products are specified at different stages.
-/

@[expose] public section

universe uι uR uF uκ uν

namespace DirectLimit

/-- Lift two rectangular factors and both prescribed products to one stage above the two
parameter stages, for a function-like family of nonunital ring homomorphisms.
The transition maps need not be injective, and the dimensions may be empty. -/
theorem exists_matrix_products
    {ι : Type uι} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    (R : ι → Type uR) [∀ i, NonUnitalNonAssocSemiring (R i)]
    {F : ∀ ⦃i j : ι⦄, i ≤ j → Type uF}
    [∀ i j (h : i ≤ j), FunLike (F h) (R i) (R j)]
    [∀ i j (h : i ≤ j), NonUnitalRingHomClass (F h) (R i) (R j)]
    (f : ∀ i j (h : i ≤ j), F h)
    [DirectedSystem R (fun i j h ↦ (f i j h : R i → R j))]
    {κ : Type uκ} [Fintype κ] {ν : Type uν} [Fintype ν]
    (i j : ι) (P : Matrix κ κ (R i)) (Q : Matrix ν ν (R j))
    (X : Matrix κ ν (DirectLimit R f)) (Y : Matrix ν κ (DirectLimit R f))
    (hXY : X * Y = P.map (NonUnitalRing.of R f i))
    (hYX : Y * X = Q.map (NonUnitalRing.of R f j)) :
    ∃ (k : ι) (hik : i ≤ k) (hjk : j ≤ k)
      (A : Matrix κ ν (R k)) (B : Matrix ν κ (R k)),
      A.map (NonUnitalRing.of R f k) = X ∧
      B.map (NonUnitalRing.of R f k) = Y ∧
      A * B = P.map (f i k hik) ∧ B * A = Q.map (f j k hjk) := by
  classical
  let z : (κ × ν) ⊕ (ν × κ) → DirectLimit R f :=
    Sum.elim (fun ab ↦ X ab.1 ab.2) (fun ab ↦ Y ab.1 ab.2)
  obtain ⟨s, Z, hZ⟩ := exists_eq_mk_of_finite f z
  let A₀ : Matrix κ ν (R s) := Matrix.of (fun a b ↦ Z (Sum.inl (a, b)))
  let B₀ : Matrix ν κ (R s) := Matrix.of (fun a b ↦ Z (Sum.inr (a, b)))
  have hA₀ : A₀.map (NonUnitalRing.of R f s) = X := by
    ext a b
    simpa only [A₀, z, Matrix.map_apply, Matrix.of_apply,
      NonUnitalRing.of_apply, Sum.elim_inl] using (hZ (Sum.inl (a, b))).symm
  have hB₀ : B₀.map (NonUnitalRing.of R f s) = Y := by
    ext a b
    simpa only [B₀, z, Matrix.map_apply, Matrix.of_apply,
      NonUnitalRing.of_apply, Sum.elim_inr] using (hZ (Sum.inr (a, b))).symm
  have hP : (A₀ * B₀).map (NonUnitalRing.of R f s) =
      P.map (NonUnitalRing.of R f i) := by
    rw [Matrix.map_mul, hA₀, hB₀]
    exact hXY
  have hQ : (B₀ * A₀).map (NonUnitalRing.of R f s) =
      Q.map (NonUnitalRing.of R f j) := by
    rw [Matrix.map_mul, hB₀, hA₀]
    exact hYX
  obtain ⟨p, hsp, hip, hp⟩ :=
    (forall_mk_eq_iff_exists_of_fixed f s i
      (fun ab : κ × κ ↦ (A₀ * B₀) ab.1 ab.2)
      (fun ab ↦ P ab.1 ab.2)).1 (by
        intro ab
        simpa only [Matrix.map_apply, NonUnitalRing.of_apply]
          using congrFun (congrFun hP ab.1) ab.2)
  obtain ⟨q, hsq, hjq, hq⟩ :=
    (forall_mk_eq_iff_exists_of_fixed f s j
      (fun ab : ν × ν ↦ (B₀ * A₀) ab.1 ab.2)
      (fun ab ↦ Q ab.1 ab.2)).1 (by
        intro ab
        simpa only [Matrix.map_apply, NonUnitalRing.of_apply]
          using congrFun (congrFun hQ ab.1) ab.2)
  obtain ⟨k, hpk, hqk⟩ := exists_ge_ge p q
  refine ⟨k, hip.trans hpk, hjq.trans hqk,
    A₀.map (f s k (hsp.trans hpk)), B₀.map (f s k (hsp.trans hpk)),
    ?_, ?_, ?_, ?_⟩
  · calc
      (A₀.map (f s k (hsp.trans hpk))).map (NonUnitalRing.of R f k) =
          A₀.map (NonUnitalRing.of R f s) := by
        ext a b
        exact NonUnitalRing.of_f (hsp.trans hpk) (A₀ a b)
      _ = X := hA₀
  · calc
      (B₀.map (f s k (hsp.trans hpk))).map (NonUnitalRing.of R f k) =
          B₀.map (NonUnitalRing.of R f s) := by
        ext a b
        exact NonUnitalRing.of_f (hsp.trans hpk) (B₀ a b)
      _ = Y := hB₀
  · rw [← Matrix.map_mul]
    funext a b
    have h := congrArg (f p k hpk) (hp (a, b))
    simpa only [Matrix.map_apply, DirectedSystem.map_map' f] using h
  · rw [← Matrix.map_mul]
    funext a b
    have h := congrArg (f q k hqk) (hq (a, b))
    simpa only [Matrix.map_apply, DirectedSystem.map_map' f] using h

end DirectLimit
