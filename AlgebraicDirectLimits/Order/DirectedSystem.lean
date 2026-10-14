/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Order.DirectedInverseSystem

/-!
# Constant directed systems

A constant family of types with identity transition functions satisfies
`DirectedSystem` over any preorder. The index and carrier universes are
independent. The identity and composition laws are available through
`DirectedSystem.map_self` and `DirectedSystem.map_map`.

## References

This extends Junyan Xu's `DirectedSystem` API in Mathlib's
[`Order.DirectedInverseSystem`](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/Order/DirectedInverseSystem.lean).
The identity-law construction generalizes Keel's constant-integer
directed-colimit example in this library.
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
