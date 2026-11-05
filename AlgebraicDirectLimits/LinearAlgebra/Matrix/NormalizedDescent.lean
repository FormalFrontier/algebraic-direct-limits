/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Colimit.DirectLimit
public import Mathlib.Data.Matrix.Mul
import AlgebraicDirectLimits.Order.DirectedSystem

/-!
# Descent of normalized rectangular matrices

Finite rectangular matrices normalized on the left and right by prescribed stage matrices
admit normalized representatives at one common later stage. The normalizing matrices need
not be idempotent, and the transition maps need not be injective.

The proof uses the finite-representative and finite-equality APIs of
`AlgebraicDirectLimits.Order.DirectedSystem`.
-/

@[expose] public section

universe uI uR uF uM uN

namespace DirectLimit

/-- A matrix fixed on the left and right by two prescribed stage matrices has a
representative with the same normalization equations at a common upper stage. -/
theorem exists_normalized_matrix
    {I : Type uI} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (R : I → Type uR) [∀ i, NonUnitalNonAssocSemiring (R i)]
    {F : ∀ ⦃i j : I⦄, i ≤ j → Type uF}
    [∀ i j (h : i ≤ j), FunLike (F h) (R i) (R j)]
    [∀ i j (h : i ≤ j), NonUnitalRingHomClass (F h) (R i) (R j)]
    (f : ∀ i j (h : i ≤ j), F h)
    [DirectedSystem R (fun i j h ↦ (f i j h : R i → R j))]
    {M : Type uM} [Fintype M] {N : Type uN} [Fintype N]
    (i j : I) (A : Matrix M M (R i)) (B : Matrix N N (R j))
    (Y : Matrix N M (DirectLimit R f))
    (hBY : B.map (NonUnitalRing.of R f j) * Y = Y)
    (hYA : Y * A.map (NonUnitalRing.of R f i) = Y) :
    ∃ (k : I) (hik : i ≤ k) (hjk : j ≤ k) (Z : Matrix N M (R k)),
      Z.map (NonUnitalRing.of R f k) = Y ∧
      B.map (f j k hjk) * Z = Z ∧ Z * A.map (f i k hik) = Z := by
  classical
  obtain ⟨s, y, hy⟩ :=
    DirectLimit.exists_eq_mk_of_finite (G := R) f
      (fun p : N × M => Y p.1 p.2)
  obtain ⟨t, hit, hjt⟩ := exists_ge_ge i j
  obtain ⟨k0, htk0, hsk0⟩ := exists_ge_ge t s
  let hi0 : i ≤ k0 := hit.trans htk0
  let hj0 : j ≤ k0 := hjt.trans htk0
  let Z0 : Matrix N M (R k0) :=
    fun n m => f s k0 hsk0 (y (n, m))
  let A0 : Matrix M M (R k0) := A.map (f i k0 hi0)
  let B0 : Matrix N N (R k0) := B.map (f j k0 hj0)
  have hZ0 : Z0.map (NonUnitalRing.of R f k0) = Y := by
    ext n m
    change (NonUnitalRing.of R f k0) (f s k0 hsk0 (y (n, m))) = Y n m
    rw [NonUnitalRing.of_f]
    exact (hy (n, m)).symm
  have hA0 : A0.map (NonUnitalRing.of R f k0) =
      A.map (NonUnitalRing.of R f i) := by
    ext a b
    change (NonUnitalRing.of R f k0) (f i k0 hi0 (A a b)) =
      (NonUnitalRing.of R f i) (A a b)
    simp only [NonUnitalRing.of_f]
  have hB0 : B0.map (NonUnitalRing.of R f k0) =
      B.map (NonUnitalRing.of R f j) := by
    ext a b
    change (NonUnitalRing.of R f k0) (f j k0 hj0 (B a b)) =
      (NonUnitalRing.of R f j) (B a b)
    simp only [NonUnitalRing.of_f]
  have hleft : (B0 * Z0).map (NonUnitalRing.of R f k0) =
      Z0.map (NonUnitalRing.of R f k0) := by
    simpa only [Matrix.map_mul, hB0, hZ0] using hBY
  have hright : (Z0 * A0).map (NonUnitalRing.of R f k0) =
      Z0.map (NonUnitalRing.of R f k0) := by
    simpa only [Matrix.map_mul, hA0, hZ0] using hYA
  -- Descend both normalization equations in one finite family.
  let a : (N × M) ⊕ (N × M) → R k0 :=
    Sum.elim (fun p => (B0 * Z0) p.1 p.2)
      (fun p => (Z0 * A0) p.1 p.2)
  let b : (N × M) ⊕ (N × M) → R k0 :=
    Sum.elim (fun p => Z0 p.1 p.2) (fun p => Z0 p.1 p.2)
  have hab : ∀ x, (⟦⟨k0, a x⟩⟧ : DirectLimit R f) = ⟦⟨k0, b x⟩⟧ := by
    intro x
    rcases x with ⟨n, m⟩ | ⟨n, m⟩
    · change (NonUnitalRing.of R f k0) ((B0 * Z0) n m) =
        (NonUnitalRing.of R f k0) (Z0 n m)
      exact congrArg (fun C : Matrix N M (DirectLimit R f) => C n m) hleft
    · change (NonUnitalRing.of R f k0) ((Z0 * A0) n m) =
        (NonUnitalRing.of R f k0) (Z0 n m)
      exact congrArg (fun C : Matrix N M (DirectLimit R f) => C n m) hright
  obtain ⟨k, hk0, hk0', habk⟩ :=
    (DirectLimit.forall_mk_eq_iff_exists_of_fixed (G := R) f k0 k0 a b).mp hab
  have hleft' : (B0 * Z0).map (f k0 k hk0) = Z0.map (f k0 k hk0) := by
    ext n m
    exact habk (Sum.inl (n, m))
  have hright' : (Z0 * A0).map (f k0 k hk0) = Z0.map (f k0 k hk0) := by
    ext n m
    exact habk (Sum.inr (n, m))
  have hcomp (a b c : I) (hab : a ≤ b) (hbc : b ≤ c) :
      (fun x : R a => f b c hbc (f a b hab x)) =
        (fun x : R a => f a c (hab.trans hbc) x) := by
    funext x
    exact DirectedSystem.map_map' f hab hbc x
  have hAcomp : A0.map (f k0 k hk0) =
      A.map (f i k (hi0.trans hk0)) :=
    congrArg (fun g : R i → R k => A.map g) (hcomp i k0 k hi0 hk0)
  have hBcomp : B0.map (f k0 k hk0) =
      B.map (f j k (hj0.trans hk0)) :=
    congrArg (fun g : R j → R k => B.map g) (hcomp j k0 k hj0 hk0)
  refine ⟨k, hi0.trans hk0, hj0.trans hk0, Z0.map (f k0 k hk0), ?_, ?_, ?_⟩
  · calc
      (Z0.map (f k0 k hk0)).map (NonUnitalRing.of R f k) =
          Z0.map (NonUnitalRing.of R f k0) := by
        ext n m
        change (NonUnitalRing.of R f k) (f k0 k hk0 (Z0 n m)) =
          (NonUnitalRing.of R f k0) (Z0 n m)
        simp only [NonUnitalRing.of_f]
      _ = Y := hZ0
  · simpa only [Matrix.map_mul, hBcomp] using hleft'
  · simpa only [Matrix.map_mul, hAcomp] using hright'

end DirectLimit
