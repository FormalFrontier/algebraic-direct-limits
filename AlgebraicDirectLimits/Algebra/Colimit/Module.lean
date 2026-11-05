/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicDirectLimits.CategoryTheory.Types.DirectLimit
public import Mathlib.Algebra.Colimit.Module
import Mathlib.CategoryTheory.Limits.Types.ColimitTypeFiltered

/-!
# Module direct limits as cocones of types

The canonical maps to `Module.DirectLimit G f` form a type-theoretic cocone over the
functor of the same transition system. Its point is the module direct limit, and
its legs are the canonical module maps.

For a nonempty directed index this cocone is colimiting. Nonemptiness is necessary:
the module direct limit over an empty index has one element, whereas the colimit
of the empty diagram of types is empty. The scalar, index and stage universes are
independent; the cocone point need not lie in the stage universe.

## References

This packages Mathlib's module direct limit from `Mathlib.Algebra.Colimit.Module`
using `DirectedSystem.typesFunctor`. The colimit property follows from Mathlib's
`Module.DirectLimit.exists_of` and `Module.DirectLimit.exists_eq_of_of_eq` through
the surjectivity and injectivity characterizations of `Functor.CoconeTypes`.
-/

@[expose] public section

universe uR uι uG

open CategoryTheory

namespace Module.DirectLimit

variable {R : Type uR} [Semiring R]
variable {ι : Type uι} [Preorder ι] [DecidableEq ι]
variable (G : ι → Type uG) [∀ i, AddCommMonoid (G i)] [∀ i, Module R (G i)]
variable (f : ∀ i j, i ≤ j → G i →ₗ[R] G j)
variable [DirectedSystem G (f · · ·)]

/-- The canonical maps to the module direct limit form a cocone of types over the
transition system. -/
noncomputable def coconeTypes :
    Functor.CoconeTypes.{max uι uG} (DirectedSystem.typesFunctor f) where
  pt := Module.DirectLimit G f
  ι i x := of R ι G f i x
  ι_naturality := by
    intro i j h
    funext x
    exact of_f

/-- The point of the canonical cocone is the module direct limit. -/
@[simp]
theorem coconeTypes_pt :
    (coconeTypes G f).pt = Module.DirectLimit G f := rfl

/-- A leg of the canonical cocone is the canonical module map. -/
@[simp]
theorem coconeTypes_ι_apply (i : ι) (x : G i) :
    (coconeTypes G f).ι i x = of R ι G f i x := rfl

/-- Over a nonempty directed index, the canonical cocone of the module direct limit
is colimiting, by Mathlib's representative and eventual-equality criteria. -/
theorem coconeTypesIsColimit [Nonempty ι] [IsDirectedOrder ι] :
    (coconeTypes G f).IsColimit := by
  refine ⟨⟨?_, ?_⟩⟩
  · apply ((coconeTypes G f).descColimitType_injective_iff_of_isFiltered').2
    intro i x y h
    have hxy : of R ι G f i x = of R ι G f i y :=
      (coconeTypes_ι_apply G f i x).symm.trans
        (h.trans (coconeTypes_ι_apply G f i y))
    obtain ⟨j, hij, hxy⟩ := exists_eq_of_of_eq hxy
    refine ⟨j, homOfLE hij, ?_⟩
    exact (DirectedSystem.typesFunctor_map_homOfLE (G := G) f hij x).trans
      (hxy.trans (DirectedSystem.typesFunctor_map_homOfLE (G := G) f hij y).symm)
  · apply ((coconeTypes G f).descColimitType_surjective_iff).2
    intro z
    obtain ⟨i, x, hx⟩ := exists_of z
    exact ⟨i, x, by simpa only [coconeTypes_pt, coconeTypes_ι_apply] using hx⟩

end Module.DirectLimit
