/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicDirectLimits.Topology.TensorProduct
public import Mathlib.Data.Rat.Cast.CharZero
public import Mathlib.Topology.Algebra.Order.Archimedean
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Instances.AddCircle.Defs

/-!
# Rational angles in the real circle and integer tensors

`AddCircle.rationalAngle` maps a rational number to its real class in the circle of
period one. Its denominator is a positive integer annihilator. Integer balancing
then shows that every pure tensor of a rational coefficient with a rational angle
vanishes in `ℚ ⊗[ℤ] AddCircle (1 : ℝ)`.

All rational angles together have dense range: this follows by composing rational
cast density with the continuous, surjective real-circle quotient map. The last
lemma applies the tensor vanishing law to the existing continuous tensor generator.

## Implementation notes

The coefficient module is purely algebraic. Density requires no topology on the
rational parameter type. Division occurs only in the rational coefficient; no
rational scalar action on the circle is used.

## References

The rational-angle and integer-balancing argument follows Formal Frontier Agents'
proof route in *Rational coefficients do not preserve tensor Hausdorffness*.
Mathlib's additive-circle construction is due to Oliver Nash; rational arithmetic
and casts to Johannes Hölzl and Mario Carneiro; quotient groups to Kevin Buzzard
and Patrick Massot; rational cast density to Yury Kudryashov; and tensor products
to Kenny Lau and Mario Carneiro. The incoming tensor-generator construction is
from the existing Algebraic Direct Limits library, following Formal Frontier
Agents' continuous-group-cohomology development and Mathlib's topological-module
category and coinduced construction by Richard Hill and Andrew Yang.
-/

@[expose] public section

open scoped TensorProduct

namespace AddCircle

/-- The class of a rational real angle in the circle of period one. -/
noncomputable def rationalAngle (q : ℚ) : AddCircle (1 : ℝ) :=
  ((q : ℝ) : AddCircle (1 : ℝ))

/-- A rational angle is obtained by casting to the reals and taking its circle class. -/
theorem rationalAngle_apply (q : ℚ) :
    rationalAngle q = ((q : ℝ) : AddCircle (1 : ℝ)) := rfl

/-- The rational-angle map uses the same quotient map as the real additive circle. -/
theorem rationalAngle_eq_mk' :
    rationalAngle =
      (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ)) :
        ℝ → AddCircle (1 : ℝ)) ∘ ((↑) : ℚ → ℝ) := rfl

/-- Integer angles represent zero in the circle of period one. -/
@[simp]
theorem rationalAngle_intCast (n : ℤ) : rationalAngle (n : ℚ) = 0 := by
  rw [rationalAngle_apply, Rat.cast_intCast, coe_eq_zero_iff]
  exact ⟨n, by rw [zsmul_eq_mul, mul_one]⟩

/-- The canonical denominator annihilates a rational angle by integer scalar multiplication. -/
theorem den_zsmul_rationalAngle (q : ℚ) :
    (q.den : ℤ) • rationalAngle q = 0 := by
  have hnum : (q.den : ℝ) * (q : ℝ) = (q.num : ℝ) := by
    simpa only [Rat.cast_mul, Rat.cast_natCast, Rat.cast_intCast] using
      congrArg (fun r : ℚ ↦ (r : ℝ)) (Rat.den_mul_eq_num q)
  rw [rationalAngle_apply, ← coe_zsmul, coe_eq_zero_iff]
  refine ⟨q.num, ?_⟩
  simpa only [zsmul_eq_mul, Int.cast_natCast, mul_one] using hnum.symm

/-- Every rational angle has a positive integer annihilator, namely its denominator. -/
theorem exists_pos_zsmul_rationalAngle_eq_zero (q : ℚ) :
    ∃ n : ℤ, 0 < n ∧ n • rationalAngle q = 0 :=
  ⟨q.den, Nat.cast_pos.mpr (Rat.pos q), den_zsmul_rationalAngle q⟩

/-- All rational angles together are dense in the usual real circle of period one. -/
theorem denseRange_rationalAngle : DenseRange rationalAngle := by
  rw [rationalAngle_eq_mk']
  exact (QuotientAddGroup.mk'_surjective (AddSubgroup.zmultiples (1 : ℝ))).denseRange.comp
    (Rat.denseRange_cast (𝕜 := ℝ)) (AddCircle.continuous_mk' (1 : ℝ))

end AddCircle

namespace TensorProduct

/-- A rational coefficient tensored over the integers with any rational angle is zero.

Only the coefficient is divided by the nonzero denominator; integer balancing
moves that denominator to the circle factor. -/
@[simp]
theorem tmul_rationalAngle_eq_zero (c q : ℚ) :
    c ⊗ₜ[ℤ] AddCircle.rationalAngle q = 0 := by
  have hden : (q.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Rat.den_ne_zero q)
  have hcoeff : (q.den : ℤ) • (c / (q.den : ℚ)) = c := by
    rw [zsmul_eq_mul, Int.cast_natCast, mul_div_cancel₀ c hden]
  calc
    c ⊗ₜ[ℤ] AddCircle.rationalAngle q =
        ((q.den : ℤ) • (c / (q.den : ℚ))) ⊗ₜ[ℤ] AddCircle.rationalAngle q := by
          rw [hcoeff]
    _ = (c / (q.den : ℚ)) ⊗ₜ[ℤ] ((q.den : ℤ) • AddCircle.rationalAngle q) :=
      TensorProduct.smul_tmul (q.den : ℤ) (c / (q.den : ℚ)) (AddCircle.rationalAngle q)
    _ = 0 := by rw [AddCircle.den_zsmul_rationalAngle, TensorProduct.tmul_zero]

end TensorProduct

namespace TopModuleCat

/-- Each continuous fixed-coefficient rational tensor generator kills every rational angle.
In particular this applies to the generator at coefficient one. -/
theorem tensorGenerator_rationalAngle (c q : ℚ) :
    tensorGenerator ℤ (ModuleCat.of ℤ ℚ) (of ℤ (AddCircle (1 : ℝ))) c
      (AddCircle.rationalAngle q) = 0 := by
  exact Eq.trans (α := TensorProduct ℤ ℚ (AddCircle (1 : ℝ)))
    (tensorGenerator_apply ℤ (ModuleCat.of ℤ ℚ) (of ℤ (AddCircle (1 : ℝ))) c
      (AddCircle.rationalAngle q))
    (TensorProduct.tmul_rationalAngle_eq_zero c q)

end TopModuleCat
