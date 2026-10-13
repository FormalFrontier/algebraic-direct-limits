/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Topology.Instances.AddCircle.Defs

/-!
# A rational-quotient detector for the real circle tensor

The rational span of `1` in `ℝ` is the image of `ℚ`. Its algebraic quotient
`AddCircle.RationalQuotient` receives an integer-linear map
`AddCircle.toRationalQuotient` from `AddCircle (1 : ℝ)`: the quotient projection
kills the integer period subgroup and therefore descends through the circle.

Rational scalar multiplication on this target gives the integer-bilinear family
`TensorProduct.rationalCircleBilinear`. Its tensor lift
`TensorProduct.rationalCircleDetector` sends `q ⊗ [x]` to the class of `(q : ℝ) * x`
modulo rational numbers. At `1 ⊗ [Real.sqrt 2]` the detector has nonzero value, so
this tensor is nonzero.

## Implementation notes

All scalar actions are the canonical ones. Rational scalars act on the algebraic
quotient, not on the circle. No topology is supplied on the quotient, and no
continuity is asserted for the descent or detector.

## References

The rational-circle example and quotient-detector proof follow Formal Frontier
Agents (Lantern), *Rational coefficients do not preserve tensor Hausdorffness*,
§5, and its stock API companion, §§4–5. The constructions reuse Mathlib's circle
(Oliver Nash), integer-generated subgroups (Chris Hughes), quotient groups
(Kevin Buzzard and Patrick Massot), spans and module quotients (Johannes Hölzl,
Mario Carneiro, Kevin Buzzard, Yury Kudryashov, Frédéric Dupuis and Heather Macbeth),
linear maps and integer actions (Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl,
Mario Carneiro, Anne Baanen, Frédéric Dupuis and Heather Macbeth), rational algebra
(Kenny Lau and Yury Kudryashov), scalar commutation (Chris Hughes and Yury
Kudryashov), field scalar actions (Robert Y. Lewis, Leonardo de Moura, Johannes
Hölzl, Mario Carneiro and Yaël Dillies), bilinear maps and tensor lifts (Kenny Lau
and Mario Carneiro), and irrationality (Mario Carneiro, Abhimanyu Pallavi Sudhir,
Jean Lo, Calle Sönne and Yury Kudryashov).
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

namespace AddCircle

/-- The algebraic rational module of real numbers modulo rational numbers,
realized as the quotient by the rational span of `1`. -/
abbrev RationalQuotient := ℝ ⧸ Submodule.span ℚ {(1 : ℝ)}

namespace RationalQuotient

/-- A real number projects to zero in the rational quotient exactly when it is
in the image of the rational cast. -/
theorem mkQ_eq_zero_iff (x : ℝ) :
    (Submodule.span ℚ {(1 : ℝ)}).mkQ x = 0 ↔ ∃ q : ℚ, (q : ℝ) = x := by
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_span_singleton]
  simp only [Rat.smul_def, mul_one]

/-- The class of `Real.sqrt 2` in the algebraic rational quotient is nonzero. -/
theorem mkQ_sqrt_two_ne_zero :
    (Submodule.span ℚ {(1 : ℝ)}).mkQ (Real.sqrt 2) ≠ 0 := by
  intro h
  obtain ⟨q, hq⟩ := (mkQ_eq_zero_iff (Real.sqrt 2)).mp h
  exact irrational_sqrt_two.ne_rat q hq.symm

end RationalQuotient

private theorem periods_le_mkQ_ker :
    AddSubgroup.zmultiples (1 : ℝ) ≤
      (Submodule.span ℚ {(1 : ℝ)}).mkQ.toAddMonoidHom.ker := by
  apply AddSubgroup.zmultiples_le.mpr
  apply AddMonoidHom.mem_ker.mpr
  change (Submodule.span ℚ {(1 : ℝ)}).mkQ (1 : ℝ) = 0
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact Submodule.mem_span_singleton_self (1 : ℝ)

/-- The integer-linear descent of the rational-quotient projection through the
real circle of period `1`. -/
def toRationalQuotient : AddCircle (1 : ℝ) →ₗ[ℤ] RationalQuotient :=
  (QuotientAddGroup.lift (AddSubgroup.zmultiples (1 : ℝ))
    (Submodule.span ℚ {(1 : ℝ)}).mkQ.toAddMonoidHom
    (by exact periods_le_mkQ_ker)).toIntLinearMap

/-- On a real representative, the circle descent agrees with the submodule
quotient projection. -/
@[simp]
theorem toRationalQuotient_coe (x : ℝ) :
    toRationalQuotient (x : AddCircle (1 : ℝ)) =
      (Submodule.span ℚ {(1 : ℝ)}).mkQ x := by
  exact QuotientAddGroup.lift_mk (AddSubgroup.zmultiples (1 : ℝ)) periods_le_mkQ_ker x

/-- Composing the descended additive map with the circle quotient map recovers
the rational-quotient projection. -/
theorem toRationalQuotient_comp_mk' :
    toRationalQuotient.toAddMonoidHom.comp
        (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))) =
      (Submodule.span ℚ {(1 : ℝ)}).mkQ.toAddMonoidHom := by
  ext x
  exact toRationalQuotient_coe x

end AddCircle

namespace TensorProduct

/-- The integer-bilinear family obtained by rationally scaling the circle's
image in the algebraic rational quotient. -/
def rationalCircleBilinear :
    ℚ →ₗ[ℤ] AddCircle (1 : ℝ) →ₗ[ℤ] AddCircle.RationalQuotient :=
  LinearMap.mk₂ ℤ (fun q m => q • AddCircle.toRationalQuotient m)
    (fun q₁ q₂ m => add_smul q₁ q₂ (AddCircle.toRationalQuotient m))
    (fun z q m => smul_assoc z q (AddCircle.toRationalQuotient m))
    (fun q m₁ m₂ => by rw [map_add, smul_add])
    (fun z q m => by
      rw [map_smul]
      exact smul_comm q z (AddCircle.toRationalQuotient m))

/-- The bilinear family evaluates by rational scalar multiplication in its
target, with no rational scalar action on the circle. -/
@[simp]
theorem rationalCircleBilinear_apply (q : ℚ) (m : AddCircle (1 : ℝ)) :
    rationalCircleBilinear q m = q • AddCircle.toRationalQuotient m :=
  rfl

/-- The algebraic tensor detector with values in real numbers modulo rational
numbers, induced by `rationalCircleBilinear`. -/
def rationalCircleDetector :
    ℚ ⊗[ℤ] AddCircle (1 : ℝ) →ₗ[ℤ] AddCircle.RationalQuotient :=
  TensorProduct.lift rationalCircleBilinear

/-- The detector's value on a pure tensor is the corresponding rational scalar
multiple of the descended circle class. -/
@[simp]
theorem rationalCircleDetector_tmul (q : ℚ) (m : AddCircle (1 : ℝ)) :
    rationalCircleDetector (q ⊗ₜ[ℤ] m) = q • AddCircle.toRationalQuotient m := by
  exact (TensorProduct.lift.tmul (f' := rationalCircleBilinear) q m).trans
    (rationalCircleBilinear_apply q m)

/-- On a real representative, the detector sends `q ⊗ [x]` to the class of
`(q : ℝ) * x` modulo rational numbers. -/
@[simp]
theorem rationalCircleDetector_tmul_coe (q : ℚ) (x : ℝ) :
    rationalCircleDetector (q ⊗ₜ[ℤ] (x : AddCircle (1 : ℝ))) =
      (Submodule.span ℚ {(1 : ℝ)}).mkQ ((q : ℝ) * x) := by
  rw [rationalCircleDetector_tmul, AddCircle.toRationalQuotient_coe, ← map_smul,
    Rat.smul_def]

/-- At rational coefficient `1`, the detector recovers the class of the real
representative in the rational quotient. -/
@[simp]
theorem rationalCircleDetector_one_tmul_coe (x : ℝ) :
    rationalCircleDetector ((1 : ℚ) ⊗ₜ[ℤ] (x : AddCircle (1 : ℝ))) =
      (Submodule.span ℚ {(1 : ℝ)}).mkQ x := by
  rw [rationalCircleDetector_tmul, AddCircle.toRationalQuotient_coe, one_smul]

/-- The quotient-detector argument of Lantern has a nonzero characteristic
value at `1 ⊗ [Real.sqrt 2]`, by `irrational_sqrt_two`. -/
theorem rationalCircleDetector_sqrt_two_ne_zero :
    rationalCircleDetector
        ((1 : ℚ) ⊗ₜ[ℤ] ((Real.sqrt 2 : ℝ) : AddCircle (1 : ℝ))) ≠ 0 := by
  rw [rationalCircleDetector_one_tmul_coe]
  exact AddCircle.RationalQuotient.mkQ_sqrt_two_ne_zero

/-- The tensor `1 ⊗ [Real.sqrt 2]` in `ℚ ⊗[ℤ] AddCircle (1 : ℝ)` is nonzero,
as detected by the algebraic rational quotient. -/
theorem rationalCircle_tensor_sqrt_two_ne_zero :
    (1 : ℚ) ⊗ₜ[ℤ] ((Real.sqrt 2 : ℝ) : AddCircle (1 : ℝ)) ≠ 0 := by
  intro h
  apply rationalCircleDetector_sqrt_two_ne_zero
  rw [h, map_zero]

end TensorProduct
