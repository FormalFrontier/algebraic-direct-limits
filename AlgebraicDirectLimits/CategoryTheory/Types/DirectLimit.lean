/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Order.DirectedInverseSystem
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.Types.Filtered

/-!
# Directed limits as cocones of types

The selected function-like transition maps of a directed system define a functor to types.
After lifting the stage carriers and the direct limit to a common universe, the quotient
constructors form a cocone. This cocone is colimiting, including over an empty directed index.

The lifting universe may contain an additional independent universe. In particular, finite
products can be packaged in one category of types without identifying the index, coordinate,
carrier or transition-data universes. The raw direct limit still uses the original selected
transition maps.

## References

The functor uses Mathlib's `DirectedSystem` laws from `Mathlib.Order.DirectedInverseSystem`.
The colimit characterization is supplied by
`CategoryTheory.Limits.Types.FilteredColimit.isColimitOf` in
`Mathlib.CategoryTheory.Limits.Types.Filtered`.
-/

@[expose] public section

universe uι uG uT u

open CategoryTheory CategoryTheory.Limits

namespace DirectedSystem

variable {ι : Type uι} [Preorder ι]
variable {G : ι → Type uG} {T : ∀ ⦃i j : ι⦄, i ≤ j → Sort uT}
variable (f : ∀ i j (h : i ≤ j), T h)
variable [∀ ⦃i j⦄ (h : i ≤ j), FunLike (T h) (G i) (G j)]
variable [DirectedSystem G (f · · ·)]

/-- The functor to types determined by the selected transition maps of a directed system. -/
def typesFunctor : ι ⥤ Type uG where
  obj := G
  map {i j} h := TypeCat.ofHom (f i j (leOfHom h))
  map_id i := by
    ext x
    exact DirectedSystem.map_self' f x
  map_comp h k := by
    ext x
    exact (DirectedSystem.map_map' f (leOfHom h) (leOfHom k) x).symm

/-- The object of the associated functor is the original stage carrier. -/
@[simp]
theorem typesFunctor_obj (i : ι) : (typesFunctor f).obj i = G i := rfl

/-- On an inequality, the associated functor acts by the selected transition map. -/
@[simp]
theorem typesFunctor_map_homOfLE {i j : ι} (h : i ≤ j) (x : G i) :
    ConcreteCategory.hom (X := G i) (Y := G j)
      ((typesFunctor f).map (homOfLE h)) x = f i j h x := rfl

end DirectedSystem

namespace DirectLimit

variable {ι : Type uι} [Preorder ι] [IsDirectedOrder ι]
variable {G : ι → Type uG} {T : ∀ ⦃i j : ι⦄, i ≤ j → Sort uT}
variable (f : ∀ i j (h : i ≤ j), T h)
variable [∀ ⦃i j⦄ (h : i ≤ j), FunLike (T h) (G i) (G j)]
variable [DirectedSystem G (f · · ·)]

/-- The quotient constructors, lifted to a common universe, form a cocone over the
functor of the original transition system. -/
def uliftCocone :
    Cocone (DirectedSystem.typesFunctor f ⋙ uliftFunctor.{max uι uG u, uG}) where
  pt := ULift.{max uι uG u} (DirectLimit G f)
  ι :=
    { app i := TypeCat.ofHom fun x ↦ ULift.up ⟦⟨i, x.down⟩⟧
      naturality := by
        intro i j h
        ext x
        exact congrArg ULift.up
          (DirectLimit.mk_apply (F := G) (f := f) i j x.down (leOfHom h)) }

/-- A leg of the lifted cocone sends a lifted coefficient to its lifted quotient class. -/
@[simp]
theorem uliftCocone_ι_app (i : ι) (x : ULift.{max uι uG u} (G i)) :
    ConcreteCategory.hom
      (X := uliftFunctor.{max uι uG u, uG}.obj (G i))
      (Y := (uliftCocone.{uι, uG, uT, u} f).pt)
      ((uliftCocone.{uι, uG, uT, u} f).ι.app i) x =
        ULift.up (⟦⟨i, x.down⟩⟧ : DirectLimit G f) := rfl

/-- The lifted quotient cocone is colimiting. Representatives and equality in the raw
quotient give the two criteria of `Types.FilteredColimit.isColimitOf`; no injectivity of
transition maps or nonemptiness of the index is required. -/
noncomputable def uliftCoconeIsColimit :
    IsColimit (uliftCocone.{uι, uG, uT, u} f :
      Cocone (DirectedSystem.typesFunctor f ⋙ uliftFunctor.{max uι uG u, uG})) := by
  refine Types.FilteredColimit.isColimitOf _ _ ?_ ?_
  · intro x
    obtain ⟨i, y, hy⟩ := DirectLimit.exists_eq_mk (F := G) f x.down
    exact ⟨i, ULift.up y, congrArg ULift.up hy⟩
  · intro i j x y h
    have h' : (⟦⟨i, x.down⟩⟧ : DirectLimit G f) = ⟦⟨j, y.down⟩⟧ :=
      congrArg ULift.down h
    obtain ⟨k, hik, hjk, hxy⟩ := Quotient.eq.mp h'
    exact ⟨k, homOfLE hik, homOfLE hjk, congrArg ULift.up hxy⟩

end DirectLimit
