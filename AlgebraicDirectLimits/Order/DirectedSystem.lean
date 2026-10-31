/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Basic.Finite.Defs
public import Mathlib.Order.DirectedInverseSystem
import Mathlib.Data.Fintype.Order

/-!
# Directed systems and finite families in direct limits

A constant family of types with identity transition functions satisfies
`DirectedSystem` over any preorder. The index and carrier universes are
independent. The identity and composition laws are available through
`DirectedSystem.map_self` and `DirectedSystem.map_map`.

Over a nonempty directed index, every finite family in a direct limit has representatives at a
common stage, for arbitrary function-like transition maps. Equality of finitely many quotient
classes can likewise be witnessed at one common stage. For families from two fixed stages,
this stage can be chosen above both, even for an empty family. Injectivity and algebraic
structure are not required.

## References

This extends Junyan Xu's `DirectedSystem` API in Mathlib's
[`Order.DirectedInverseSystem`](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/Order/DirectedInverseSystem.lean).
The identity-law construction generalizes Keel's constant-integer
directed-colimit example in this library.
The finite-family results extend the simultaneous-representative and simultaneous-equality
theorems for first-order structures formalized by Aaron Anderson and Gabin Kolly in
`Mathlib.ModelTheory.DirectLimit`.
-/

@[expose] public section

universe u v

namespace DirectedSystem

/-- A constant family with identity transition functions is a directed system
over any preorder, without directedness or nonemptiness assumptions. -/
instance const {ι : Type u} [Preorder ι] (A : Type v) :
    DirectedSystem (fun _ : ι => A) (fun _ _ _ => id) where
  map_self := by intros; rfl
  map_map := by intros; rfl

end DirectedSystem

universe uι uG uT uα

namespace DirectLimit

section FiniteEquality

variable {ι : Type uι} [Preorder ι] [IsDirectedOrder ι]
variable {G : ι → Type uG} {T : ∀ ⦃i j : ι⦄, i ≤ j → Sort uT}
variable (f : ∀ i j (h : i ≤ j), T h)
variable [∀ ⦃i j⦄ (h : i ≤ j), FunLike (T h) (G i) (G j)]
variable [DirectedSystem G (f · · ·)]

/-- Two finite families have the same quotient classes if and only if their values
agree after transport to one common stage. The index must be nonempty even when the
family is empty. -/
theorem forall_mk_eq_iff_exists [Nonempty ι] {α : Type uα} [Finite α]
    (x y : α → Σ i, G i) :
    (∀ a, (⟦x a⟧ : DirectLimit G f) = ⟦y a⟧) ↔
      ∃ (k : ι) (hx : ∀ a, (x a).1 ≤ k) (hy : ∀ a, (y a).1 ≤ k),
        (fun a ↦ f (x a).1 k (hx a) (x a).2) =
          (fun a ↦ f (y a).1 k (hy a) (y a).2) := by
  classical
  constructor
  · intro h
    have h' (a : α) :
        ∃ (k : ι) (hx : (x a).1 ≤ k) (hy : (y a).1 ≤ k),
          f (x a).1 k hx (x a).2 = f (y a).1 k hy (y a).2 :=
      Quotient.eq.mp (h a)
    choose k hx hy hk using h'
    obtain ⟨m, hm⟩ := Finite.exists_le k
    refine ⟨m, fun a ↦ (hx a).trans (hm a), fun a ↦ (hy a).trans (hm a), ?_⟩
    funext a
    rw [← DirectedSystem.map_map' f (hx a) (hm a),
      ← DirectedSystem.map_map' f (hy a) (hm a), hk a]
  · rintro ⟨k, hx, hy, h⟩ a
    exact Quotient.sound ⟨k, hx a, hy a, congrFun h a⟩

/-- Equality of two finite families from fixed stages can be witnessed at one stage
above both input stages, including when the family is empty. -/
theorem forall_mk_eq_iff_exists_of_fixed {α : Type uα} [Finite α]
    (i j : ι) (a : α → G i) (b : α → G j) :
    (∀ x, (⟦⟨i, a x⟩⟧ : DirectLimit G f) = ⟦⟨j, b x⟩⟧) ↔
      ∃ (k : ι) (hik : i ≤ k) (hjk : j ≤ k),
        ∀ x, f i k hik (a x) = f j k hjk (b x) := by
  classical
  let : Nonempty ι := ⟨i⟩
  constructor
  · intro h
    obtain ⟨k, hx, hy, hk⟩ :=
      (forall_mk_eq_iff_exists f (fun x ↦ ⟨i, a x⟩) (fun x ↦ ⟨j, b x⟩)).1 h
    obtain ⟨l, hil, hjl⟩ := exists_ge_ge i j
    obtain ⟨m, hkm, hlm⟩ := exists_ge_ge k l
    refine ⟨m, hil.trans hlm, hjl.trans hlm, ?_⟩
    intro x
    have eq := congrArg (f k m hkm) (congrFun hk x)
    simpa only [DirectedSystem.map_map'] using eq
  · rintro ⟨k, hik, hjk, h⟩ x
    exact Quotient.sound ⟨k, hik, hjk, h x⟩

end FiniteEquality

variable {ι : Type uι} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
variable {G : ι → Type uG} {T : ∀ ⦃i j : ι⦄, i ≤ j → Sort uT}
variable (f : ∀ i j (h : i ≤ j), T h)
variable [∀ ⦃i j⦄ (h : i ≤ j), FunLike (T h) (G i) (G j)]
variable [DirectedSystem G (f · · ·)]

/-- A finite family in a directed limit can be represented at a common stage.
The nonempty index assumption is necessary even when the family is empty. -/
theorem exists_eq_mk_of_finite {α : Type uα} [Finite α]
    (p : α → DirectLimit G f) :
    ∃ (i : ι) (q : α → G i), ∀ a, p a = ⟦⟨i, q a⟩⟧ := by
  classical
  choose i x hx using fun a ↦ DirectLimit.exists_eq_mk f (p a)
  obtain ⟨j, hj⟩ := Finite.exists_le i
  refine ⟨j, fun a ↦ f (i a) j (hj a) (x a), ?_⟩
  intro a
  exact (hx a).trans (DirectLimit.eq_of_le ⟨i a, x a⟩ j (hj a))

end DirectLimit
