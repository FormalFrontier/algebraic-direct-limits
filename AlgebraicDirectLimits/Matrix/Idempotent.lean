/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Colimit.DirectLimit
public import Mathlib.Data.Matrix.Mul
import AlgebraicDirectLimits.Order.DirectedSystem
import Mathlib.Data.Fintype.Order

/-!
# Idempotent matrices in directed limits

Finite idempotent matrices over a directed limit descend to a component. A matrix
at a component whose image is idempotent becomes idempotent after passing to a
sufficiently large component. Transition maps need not be injective.

These are results about matrix equations over nonunital, nonassociative semirings.
Their interpretation in terms of projective modules requires additional ring
hypotheses and is not asserted here.

## References

* Charles A. Weibel, *The K-book: An introduction to algebraic K-theory*.
-/

@[expose] public section

universe uι uR uκ uν

namespace DirectLimit

variable {ι : Type uι} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
variable (R : ι → Type uR) [∀ i, NonUnitalNonAssocSemiring (R i)]
variable (f : ∀ i j, i ≤ j → R i →ₙ+* R j)
variable [DirectedSystem R (fun i j h ↦ (f i j h : R i → R j))]
private theorem exists_matrix_representation {κ : Type uκ} [Finite κ]
    {ν : Type uν} [Finite ν] (p : Matrix κ ν (DirectLimit R f)) :
    ∃ (i : ι) (q : Matrix κ ν (R i)), q.map (NonUnitalRing.of R f i) = p := by
  obtain ⟨i, q, hq⟩ := exists_eq_mk_of_finite f (fun ab : κ × ν ↦ p ab.1 ab.2)
  refine ⟨i, Matrix.of (fun a b ↦ q (a, b)), ?_⟩
  ext a b
  simpa only [Matrix.map_apply, Matrix.of_apply, NonUnitalRing.of_apply]
    using (hq (a, b)).symm

variable {κ : Type uκ} [Fintype κ]

/-- A matrix whose image in the limit is idempotent becomes idempotent at a
later stage, without assuming injectivity of the transition maps.

This is the finite-equation argument used by Charles A. Weibel in *The K-book*,
formulated here for matrix equations over nonunital, nonassociative semirings. -/
theorem exists_idempotent_matrix_map (i : ι) (p : Matrix κ κ (R i))
    (hp : p.map (DirectLimit.NonUnitalRing.of R f i) *
      p.map (DirectLimit.NonUnitalRing.of R f i) =
        p.map (DirectLimit.NonUnitalRing.of R f i)) :
    ∃ (j : ι) (hij : i ≤ j),
      (p.map (f i j hij)) * (p.map (f i j hij)) = p.map (f i j hij) := by
  classical
  have hp' : (p * p).map (NonUnitalRing.of R f i) =
      p.map (NonUnitalRing.of R f i) := by
    rw [Matrix.map_mul]
    exact hp
  have hentry (ab : κ × κ) :
      ∃ (j : ι) (hij : i ≤ j),
        f i j hij ((p * p) ab.1 ab.2) = f i j hij (p ab.1 ab.2) := by
    have hab := congrFun (congrFun hp' ab.1) ab.2
    simp only [Matrix.map_apply, NonUnitalRing.of_apply] at hab
    obtain ⟨j, hij, hij', he⟩ := Quotient.eq.mp hab
    exact ⟨j, hij, he⟩
  choose j hij he using hentry
  obtain ⟨k, hk⟩ := Finite.exists_le j
  obtain ⟨l, hil, hkl⟩ := exists_ge_ge i k
  refine ⟨l, hil, ?_⟩
  rw [← Matrix.map_mul]
  funext a b
  have h := congrArg (f (j (a, b)) l ((hk (a, b)).trans hkl)) (he (a, b))
  simpa only [Matrix.map_apply, DirectedSystem.map_map' f] using h

/-- A finite idempotent matrix over a directed limit is represented by an
idempotent matrix over one component.

This is the finite-matrix descent argument used by Charles A. Weibel in *The K-book*,
extended here to nonunital, nonassociative semirings without a module interpretation. -/
theorem exists_idempotent_matrix
    (p : Matrix κ κ (DirectLimit R f)) (hp : p * p = p) :
    ∃ (i : ι) (q : Matrix κ κ (R i)), q * q = q ∧
      q.map (DirectLimit.NonUnitalRing.of R f i) = p := by
  obtain ⟨i, q, hq⟩ := exists_matrix_representation R f p
  obtain ⟨j, hij, hj⟩ := exists_idempotent_matrix_map R f i q (by simpa only [hq] using hp)
  refine ⟨j, q.map (f i j hij), hj, ?_⟩
  ext a b
  simpa only [Matrix.map_apply, NonUnitalRing.of_f] using congrFun (congrFun hq a) b

end DirectLimit
