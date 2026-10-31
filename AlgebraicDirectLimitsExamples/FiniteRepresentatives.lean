/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicDirectLimits.Order.DirectedSystem
public import Mathlib.ModelTheory.DirectLimit

/-!
# Simultaneous representatives for directed limits of structures

The finite-family theorem for arbitrary function-like transition maps recovers the
function-valued simultaneous-representative statement for first-order structures from
`Mathlib.ModelTheory.DirectLimit`, formalized by Aaron Anderson and Gabin Kolly.
-/

@[expose] public section

universe uι uG uα

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
