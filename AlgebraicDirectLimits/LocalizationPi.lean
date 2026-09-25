/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Localization.Pi

/-!
# Localization and countable products

This module gives the canonical comparison from localization of a countable product at a
constant element to the product of the corresponding localizations.  It proves that this map is
not surjective when the element is nonzero and not a unit in a commutative domain.
-/

public section

namespace Localization

variable {R : Type*} [CommRing R]

/-- The canonical map from localization of a countable product at the constant tuple `r` to the
product of the localizations away from `r`. -/
noncomputable def awayPiComparison (r : R) :
    Away (fun _ : ℕ ↦ r) →+* (∀ _ : ℕ, Away r) :=
  letI (i : ℕ) : IsLocalization
      ((Submonoid.powers (fun _ : ℕ ↦ r)).map (Pi.evalRingHom (fun _ : ℕ ↦ R) i))
      (Away r) := by
    rw [Submonoid.map_powers]
    change IsLocalization (Submonoid.powers r) (Away r)
    infer_instance
  IsLocalization.lift <|
    IsLocalization.isUnit_piRingHom_algebraMap_comp_piEvalRingHom
      (fun _ : ℕ ↦ R) (fun _ : ℕ ↦ Away r) (Submonoid.powers (fun _ : ℕ ↦ r))

/-- The comparison map agrees coordinatewise with the localization maps on the original
countable product. -/
@[simp]
theorem awayPiComparison_algebraMap (r : R) (a : ℕ → R) :
    awayPiComparison r (algebraMap (ℕ → R) (Away (fun _ : ℕ ↦ r)) a) =
      fun i ↦ algebraMap R (Away r) (a i) := by
  simp [awayPiComparison, IsLocalization.lift_eq]
  rfl

/-- If `r` is nonzero and not a unit in a commutative domain, localization of a countable
product at the constant tuple `r` does not surject onto the product of the localizations away
from `r`. -/
theorem awayPiComparison_not_surjective [IsDomain R] (r : R) (hr : r ≠ 0)
    (hr_unit : ¬ IsUnit r) : ¬ Function.Surjective (awayPiComparison r) := by
  intro hsurj
  let z : ℕ → Away r := fun n ↦ IsLocalization.Away.invSelf r ^ n
  obtain ⟨x, hx⟩ := hsurj z
  let a := IsLocalization.Away.sec (fun _ : ℕ ↦ r) x
  have hsec := IsLocalization.Away.sec_spec (fun _ : ℕ ↦ r) x
  have htarget :
      z * (fun _ : ℕ ↦ algebraMap R (Away r) (r ^ a.2)) =
        fun n ↦ algebraMap R (Away r) (a.1 n) := by
    calc
      z * (fun _ : ℕ ↦ algebraMap R (Away r) (r ^ a.2)) =
          awayPiComparison r x * awayPiComparison r
            (algebraMap (ℕ → R) (Away (fun _ : ℕ ↦ r)) ((fun _ : ℕ ↦ r) ^ a.2)) := by
              rw [hx, awayPiComparison_algebraMap]
              rfl
      _ = awayPiComparison r
          (x * algebraMap (ℕ → R) (Away (fun _ : ℕ ↦ r)) ((fun _ : ℕ ↦ r) ^ a.2)) :=
            (awayPiComparison r).map_mul _ _ |>.symm
      _ = awayPiComparison r
          (algebraMap (ℕ → R) (Away (fun _ : ℕ ↦ r)) a.1) := by rw [hsec]
      _ = fun n ↦ algebraMap R (Away r) (a.1 n) := awayPiComparison_algebraMap r a.1
  have hcoord := congr_fun htarget (a.2 + 1)
  have hinv : IsLocalization.Away.invSelf r =
      algebraMap R (Away r) (a.1 (a.2 + 1)) := by
    change IsLocalization.Away.invSelf r ^ (a.2 + 1) *
        algebraMap R (Away r) (r ^ a.2) =
      algebraMap R (Away r) (a.1 (a.2 + 1)) at hcoord
    rw [map_pow] at hcoord
    have hcancel : IsLocalization.Away.invSelf r ^ (a.2 + 1) *
        algebraMap R (Away r) r ^ a.2 = IsLocalization.Away.invSelf r := by
      rw [pow_succ]
      calc
        IsLocalization.Away.invSelf r ^ a.2 * IsLocalization.Away.invSelf r *
            algebraMap R (Away r) r ^ a.2 =
            (IsLocalization.Away.invSelf r * algebraMap R (Away r) r) ^ a.2 *
              IsLocalization.Away.invSelf r := by
                rw [mul_pow]
                ac_rfl
        _ = IsLocalization.Away.invSelf r := by
          rw [mul_comm (IsLocalization.Away.invSelf r),
            IsLocalization.Away.mul_invSelf]
          simp
    exact hcancel.symm.trans hcoord
  have hone : algebraMap R (Away r) 1 =
      algebraMap R (Away r) (r * a.1 (a.2 + 1)) := by
    rw [map_one, map_mul, ← hinv, IsLocalization.Away.mul_invSelf]
  have : r * a.1 (a.2 + 1) = 1 := by
    exact (IsLocalization.injective (Away r)
      (powers_le_nonZeroDivisors_of_noZeroDivisors hr)) hone.symm
  exact hr_unit (IsUnit.of_mul_eq_one _ this)

end Localization
