/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.TwoSidedIdeal.Operations

/-!
# Filtered colimits of simple rings

This file proves that a filtered colimit of simple rings is simple. No
injectivity hypothesis is needed: simplicity makes every transition map
injective, and filtered-colimit equality then makes each canonical stage map
injective.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace RingCat.FilteredColimits

variable {J : Type v} [SmallCategory J] [IsFiltered J]
variable (F : J ⥤ RingCat.{max v u})

private theorem colimitCocone_ι_injective
    (hF : ∀ j, IsSimpleRing (F.obj j)) (j : J) :
    Function.Injective ((colimitCocone F).ι.app j).hom := by
  let _ : PreservesFilteredColimitsOfSize.{v, v} (forget RingCat.{max v u}) :=
    preservesFilteredColimitsOfSize_shrink _
  intro x y hxy
  obtain ⟨k, f, hf⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff'
      (isColimitOfPreserves (forget RingCat)
        (colimitCoconeIsColimit F)) x y).mp hxy
  let _ : IsSimpleRing (F.obj j) := hF j
  let _ : IsSimpleRing (F.obj k) := hF k
  exact (F.map f).hom.injective hf

/-- A filtered colimit of simple rings is simple. -/
theorem colimit_isSimpleRing
    (hF : ∀ j, IsSimpleRing (F.obj j)) :
    IsSimpleRing (colimit F) := by
  let _ : PreservesFilteredColimitsOfSize.{v, v} (forget RingCat.{max v u}) :=
    preservesFilteredColimitsOfSize_shrink _
  let _ : Nonempty J := IsFiltered.nonempty
  let j : J := Classical.arbitrary J
  let _ : IsSimpleRing (F.obj j) := hF j
  let _ : Nontrivial (colimit F) := (colimitCocone_ι_injective F hF j).nontrivial
  apply IsSimpleRing.of_eq_bot_or_eq_top
  intro I
  by_cases hI : I = ⊥
  · exact Or.inl hI
  · right
    obtain ⟨x, hxI, hx0 : x ≠ 0⟩ :=
      SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hI : (⊥ : TwoSidedIdeal (colimit F)) < I)
    obtain ⟨k, a, ha⟩ :=
      Types.jointly_surjective_of_isColimit
        (isColimitOfPreserves (forget RingCat)
          (colimitCoconeIsColimit F)) x
    change F.obj k at a
    let _ : IsSimpleRing (F.obj k) := hF k
    let f : F.obj k →+* colimit F := ((colimitCocone F).ι.app k).hom
    change f a = x at ha
    have ha0 : a ≠ 0 := by
      intro ha0
      apply hx0
      rw [← ha, ha0, map_zero]
    have haI : a ∈ I.comap f := by
      rw [TwoSidedIdeal.mem_comap, ha]
      exact hxI
    have h1 : (1 : F.obj k) ∈ I.comap f :=
      IsSimpleRing.one_mem_of_ne_zero_mem (I.comap f) ha0 haI
    apply TwoSidedIdeal.eq_top
    simpa only [TwoSidedIdeal.mem_comap, map_one] using h1

end RingCat.FilteredColimits
