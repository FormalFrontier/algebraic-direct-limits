/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Colimit.DirectLimit

/-!
# Zero in direct limits with function-like transition maps

The canonical nullary-map construction of zero extends to hom-types in `Sort`.
For hom-types in `Type` it agrees with Mathlib's canonical zero. Representing this
zero at any specified stage requires preservation of zero only by the selected
transition maps, not by every inhabitant of the hom-types.
-/

@[expose] public section

universe uι uG uT

namespace DirectLimit

section SortHom

variable {ι : Type uι} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
variable {G : ι → Type uG} {T : ∀ ⦃i j : ι⦄, i ≤ j → Sort uT}
variable (f : ∀ i j (h : i ≤ j), T h)
variable [∀ ⦃i j⦄ (h : i ≤ j), FunLike (T h) (G i) (G j)]
variable [DirectedSystem G (f · · ·)] [∀ i, Zero (G i)]

/-- The canonical zero, allowing function-like hom-types in `Sort`. -/
@[instance_reducible]
noncomputable def zeroOfSort : Zero (DirectLimit G f) where
  zero := map₀ f (fun _ ↦ 0)

end SortHom

section TypeHom

variable {ι : Type uι} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
variable {G : ι → Type uG} {T : ∀ ⦃i j : ι⦄, i ≤ j → Type uT}
variable (f : ∀ i j (h : i ≤ j), T h)
variable [∀ ⦃i j⦄ (h : i ≤ j), FunLike (T h) (G i) (G j)]
variable [DirectedSystem G (f · · ·)] [∀ i, Zero (G i)]

/-- The `Sort`-general construction agrees with the canonical `Type`-case zero. -/
theorem zeroOfSort_eq_canonical :
    zeroOfSort f = (inferInstance : Zero (DirectLimit G f)) := by
  rfl

end TypeHom

attribute [instance 100] zeroOfSort

section SelectedMaps

variable {ι : Type uι} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
variable {G : ι → Type uG} {T : ∀ ⦃i j : ι⦄, i ≤ j → Sort uT}
variable (f : ∀ i j (h : i ≤ j), T h)
variable [∀ ⦃i j⦄ (h : i ≤ j), FunLike (T h) (G i) (G j)]
variable [DirectedSystem G (f · · ·)] [∀ i, Zero (G i)]

/-- Zero is represented by zero at any stage if the selected maps preserve zero. -/
theorem zero_eq_mk_of_map_zero
    (hzero : ∀ i j (h : i ≤ j), f i j h 0 = 0) (i : ι) :
    (0 : DirectLimit G f) = ⟦⟨i, 0⟩⟧ := by
  exact map₀_def f (fun _ ↦ 0) hzero i

end SelectedMaps

end DirectLimit
