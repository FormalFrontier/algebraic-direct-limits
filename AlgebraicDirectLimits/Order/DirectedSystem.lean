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
common stage, for arbitrary function-like transition maps. Injectivity and algebraic structure
are not required.

## References

This extends Junyan Xu's `DirectedSystem` API in Mathlib's
[`Order.DirectedInverseSystem`](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/Order/DirectedInverseSystem.lean).
The identity-law construction generalizes Keel's constant-integer
directed-colimit example in this library.
The finite-family result extends the simultaneous-representative theorem for first-order
structures formalized by Aaron Anderson and Gabin Kolly in `Mathlib.ModelTheory.DirectLimit`.
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
