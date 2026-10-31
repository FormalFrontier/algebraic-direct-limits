/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicDirectLimits.Order.DirectedSystem
public import Mathlib.ModelTheory.DirectLimit
import Mathlib.Data.Matrix.Mul

/-!
# Finite representatives and simultaneous equality in directed limits

The finite-family theorem for arbitrary function-like transition maps recovers the
function-valued simultaneous-representative statement for first-order structures from
`Mathlib.ModelTheory.DirectLimit`, formalized by Aaron Anderson and Gabin Kolly.
The simultaneous-equality theorem also recovers their function-valued `unify` equality
for the original sigma representatives and setoid. A pair of rectangular
matrix-product equations is witnessed at one later stage over nonunital, nonassociative
semirings, without injectivity assumptions.
-/

@[expose] public section

universe uι uG uα uR uκ uν

open FirstOrder

variable {ι : Type uι} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]

example {L : FirstOrder.Language} (G : ι → Type uG)
    [∀ i, L.Structure (G i)]
    (f : ∀ i j, i ≤ j → G i ↪[L] G j)
    [DirectedSystem G (fun i j h ↦ f i j h)]
    {α : Type uα} [Finite α]
    (p : α → FirstOrder.Language.DirectLimit G f) :
    ∃ (i : ι) (q : α → G i), p = fun a ↦
      (⟦FirstOrder.Language.Structure.Sigma.mk f i (q a)⟧ :
        FirstOrder.Language.DirectLimit G f) := by
  obtain ⟨i, q, hq⟩ := DirectLimit.exists_eq_mk_of_finite f p
  exact ⟨i, q, funext hq⟩

section FirstOrder

open FirstOrder Set

variable {L : Language} {ι : Type uι} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
variable {G : ι → Type uG} [∀ i, L.Structure (G i)]
variable (f : ∀ i j, i ≤ j → G i ↪[L] G j)
variable [DirectedSystem G (fun i j h ↦ f i j h)]

attribute [local instance] FirstOrder.Language.DirectLimit.setoid

example {α : Type uα} [Finite α] {x y : α → FirstOrder.Language.Structure.Sigma f} (xy : x ≈ y) :
    ∃ (i : ι) (hx : i ∈ upperBounds (range (Sigma.fst ∘ x)))
      (hy : i ∈ upperBounds (range (Sigma.fst ∘ y))),
      FirstOrder.Language.DirectLimit.unify f x i hx =
        FirstOrder.Language.DirectLimit.unify f y i hy := by
  have h : ∀ a, (⟦x a⟧ : _root_.DirectLimit G f) = ⟦y a⟧ :=
    fun a ↦ Quotient.sound (xy a)
  obtain ⟨i, hx, hy, hxy⟩ := (_root_.DirectLimit.forall_mk_eq_iff_exists f x y).1 h
  have hx' : i ∈ upperBounds (range (Sigma.fst ∘ x)) := by
    rintro _ ⟨a, rfl⟩
    exact hx a
  have hy' : i ∈ upperBounds (range (Sigma.fst ∘ y)) := by
    rintro _ ⟨a, rfl⟩
    exact hy a
  exact ⟨i, hx', hy', hxy⟩

end FirstOrder

section Matrix

variable {ι : Type uι} [Preorder ι] [IsDirectedOrder ι]
variable {R : ι → Type uR} [∀ i, NonUnitalNonAssocSemiring (R i)]
variable (f : ∀ i j, i ≤ j → R i →ₙ+* R j)
variable [DirectedSystem R (fun i j h ↦ (f i j h : R i → R j))]
variable {κ : Type uκ} [Fintype κ] {ν : Type uν} [Fintype ν]

example (i j : ι) (P : Matrix κ κ (R i)) (Q : Matrix ν ν (R i))
    (X : Matrix κ ν (R j)) (Y : Matrix ν κ (R j))
    (hP : ∀ a b, (⟦⟨j, (X * Y) a b⟩⟧ : DirectLimit R f) = ⟦⟨i, P a b⟩⟧)
    (hQ : ∀ a b, (⟦⟨j, (Y * X) a b⟩⟧ : DirectLimit R f) = ⟦⟨i, Q a b⟩⟧) :
    ∃ (k : ι) (hjk : j ≤ k) (hik : i ≤ k),
      X.map (f j k hjk) * Y.map (f j k hjk) = P.map (f i k hik) ∧
        Y.map (f j k hjk) * X.map (f j k hjk) = Q.map (f i k hik) := by
  let a : (κ × κ) ⊕ (ν × ν) → R j :=
    Sum.elim (fun ab ↦ (X * Y) ab.1 ab.2) (fun ab ↦ (Y * X) ab.1 ab.2)
  let b : (κ × κ) ⊕ (ν × ν) → R i :=
    Sum.elim (fun ab ↦ P ab.1 ab.2) (fun ab ↦ Q ab.1 ab.2)
  have h (c : (κ × κ) ⊕ (ν × ν)) :
      (⟦⟨j, a c⟩⟧ : DirectLimit R f) = ⟦⟨i, b c⟩⟧ := by
    cases c with
    | inl ab => exact hP ab.1 ab.2
    | inr ab => exact hQ ab.1 ab.2
  obtain ⟨k, hjk, hik, hk⟩ := (DirectLimit.forall_mk_eq_iff_exists_of_fixed f j i a b).1 h
  refine ⟨k, hjk, hik, ?_, ?_⟩
  · rw [← Matrix.map_mul]
    funext s t
    exact hk (.inl (s, t))
  · rw [← Matrix.map_mul]
    funext s t
    exact hk (.inr (s, t))

end Matrix
