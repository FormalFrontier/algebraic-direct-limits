/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

public import AlgebraicDirectLimits.CofinalGroupCompletion
public import Mathlib.Algebra.Group.PUnit

/-! A standalone downstream consumer of the public cofinal group-completion API. -/

public section

namespace CofinalGroupCompletionClient

open Algebra.GrothendieckAddGroup

universe v

private theorem localization_of_top_saturation {M : Type v} [AddCommMonoid M] (L : AddSubmonoid M)
    (hL : L.saturation = ⊤) : AddSubmonoid.IsLocalizationMap L (of (M := M)) :=
  isLocalizationMap_of_saturation_eq_top L hL

private theorem denominator_representation {M : Type v} [AddCommMonoid M] (L : AddSubmonoid M)
    (hL : L.saturation = ⊤) (z : Algebra.GrothendieckAddGroup M) :
    ∃ m : M, ∃ l : L, z = of m - of (l : M) :=
  exists_cofinal_denominator L hL z

private theorem cofinal_stabilizer_characterization {M : Type v} [AddCommMonoid M] (L : AddSubmonoid M)
    (hL : L.saturation = ⊤) (m n : M) :
    of m = of n ↔ ∃ l : L, m + (l : M) = n + (l : M) :=
  of_eq_iff_exists_cofinal_stabilizer L hL m n

private theorem inclusion_completion_injective {M : Type v} [AddCommMonoid M] (L : AddSubmonoid M)
    (hL : L.saturation = ⊤) :
    Function.Injective (lift ((of (M := M)).comp L.subtype)) :=
  lift_subtype_injective L hL

/-- The even natural numbers form a proper cofinal submonoid. -/
def evens : AddSubmonoid ℕ where
  carrier := {n | ∃ k, n = k + k}
  zero_mem' := ⟨0, rfl⟩
  add_mem' := by
    rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
    exact ⟨i + j, by ac_rfl⟩

theorem evens_saturation : evens.saturation = ⊤ := by
  ext n
  constructor
  · intro _
    trivial
  · intro _
    exact AddSubmonoid.mem_saturation_iff.mpr ⟨n, n, rfl⟩

theorem evens_proper : (1 : ℕ) ∉ evens := by
  rintro ⟨k, hk⟩
  omega

theorem evens_completion_injective :
    Function.Injective (lift ((of (M := ℕ)).comp evens.subtype)) :=
  lift_subtype_injective evens evens_saturation

theorem evens_denominators (z : Algebra.GrothendieckAddGroup ℕ) :
    ∃ m : ℕ, ∃ l : evens, z = of m - of (l : ℕ) :=
  exists_cofinal_denominator evens evens_saturation z

/-- Multiplicative natural numbers regarded additively are noncancellative;
their canonical map into the completion identifies zero and one. -/
theorem noncancellative_canonical_map_not_injective :
    ¬ Function.Injective (of (M := Additive ℕ)) := by
  intro hinj
  have h : of (Additive.ofMul (0 : ℕ)) = of (Additive.ofMul (1 : ℕ)) :=
    (of_eq_iff_exists_cofinal_stabilizer (⊤ : AddSubmonoid (Additive ℕ))
      AddSubmonoid.saturation_top _ _).mpr ⟨⟨Additive.ofMul 0, trivial⟩, rfl⟩
  exact Nat.zero_ne_one (congrArg Additive.toMul (hinj h))

theorem noncancellative_completion_injective :
    Function.Injective (lift ((of (M := Additive ℕ)).comp
      (⊤ : AddSubmonoid (Additive ℕ)).subtype)) :=
  lift_subtype_injective _ AddSubmonoid.saturation_top

theorem punit_completion_injective :
    Function.Injective (lift ((of (M := PUnit)).comp
      (⊤ : AddSubmonoid PUnit).subtype)) :=
  lift_subtype_injective _ AddSubmonoid.saturation_top

#check @isLocalizationMap_of_saturation_eq_top
#check @exists_cofinal_denominator
#check @of_eq_iff_exists_cofinal_stabilizer
#check @lift_subtype_injective
#print axioms isLocalizationMap_of_saturation_eq_top
#print axioms exists_cofinal_denominator
#print axioms of_eq_iff_exists_cofinal_stabilizer
#print axioms lift_subtype_injective
#print axioms localization_of_top_saturation
#print axioms denominator_representation
#print axioms cofinal_stabilizer_characterization
#print axioms inclusion_completion_injective
#print axioms evens_saturation
#print axioms evens_proper
#print axioms evens_completion_injective
#print axioms evens_denominators
#print axioms noncancellative_canonical_map_not_injective
#print axioms noncancellative_completion_injective
#print axioms punit_completion_injective

end CofinalGroupCompletionClient
