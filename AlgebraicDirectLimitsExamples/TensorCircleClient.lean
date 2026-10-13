/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicDirectLimitsExamples.TensorCircleModel
public import AlgebraicDirectLimits.Topology.TensorCircle.Detector
public import AlgebraicDirectLimits.Topology.TensorCircle.RationalAngles

/-!
# Non-Hausdorffness of the rational-circle tensor

This file combines the rational coefficient module, the usual real circle, the
algebraic rational-quotient detector and the dense family of rational angles.
`circleTensorDetector` is an integer-linear map on `rationalCircleTensor` itself.
It sends a pure tensor `q ⊗ [x]` to the class of `(q : ℝ) * x` modulo rationals.
Composing it with the continuous generator at coefficient `1` recovers the
circle's integer-linear descent to the rational quotient.

The detector is nonzero on `irrationalGenerator`, whereas the generator kills
every rational angle. The half-angle gives a nonzero circle point killed by the
generator, in contrast with the integer angles, which are already zero in the
circle. `rationalCircle_properties` collects the supporting properties of these
fixed modules and maps without extra hypotheses.

`not_t2Space_rationalCircleTensor` proves that this one-sided tensor is not
Hausdorff. If it were Hausdorff, the continuous generator and the zero map would
agree everywhere because they agree on the dense rational angles. This would
contradict the nonzero generator value at `[√2]`. Thus flat rational coefficients
do not preserve tensor Hausdorffness, even with a compact Hausdorff right factor.

## Implementation notes

The detector target is purely algebraic: no topology or continuity is supplied
for it. Only the incoming tensor generator is asserted continuous. Rational
scalars act on the coefficient and the rational quotient, not on the circle.
The non-Hausdorffness proof uses continuity of the generator and density of the
rational angles, not continuity of the detector.

## References

* Formal Frontier Agents (Lantern), *Rational coefficients do not preserve tensor
  Hausdorffness*, §§2–5, for the rational-circle model, dense rational angles and
  algebraic quotient-detector argument, and its stock API companion, §§2–5.
* `AlgebraicDirectLimitsExamples.TensorCircleModel`,
  `AlgebraicDirectLimits.Topology.TensorCircle.Detector` and
  `AlgebraicDirectLimits.Topology.TensorCircle.RationalAngles`, by Formal Frontier
  Agents, for the model, detector and rational-angle characteristic APIs.
* Mathlib's additive-circle construction, by Oliver Nash, for representatives in
  a fundamental interval, and its ordered-field API for the half-angle boundary.
  The providers reuse Mathlib's localization flatness, integer tensor balancing,
  algebraic quotients, rational density and irrationality of `Real.sqrt 2`.
* Mathlib's `Continuous.ext_on` in `Topology.Separation.Hausdorff`, by
  Johannes Hölzl and Mario Carneiro, for equality of continuous maps on a dense set.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

namespace TensorCircleExamples

/-- The algebraic rational-quotient detector on the one-sided circle tensor. -/
def circleTensorDetector : rationalCircleTensor →ₗ[ℤ] AddCircle.RationalQuotient :=
  TensorProduct.rationalCircleDetector

/-- The detector sends a pure tensor to the rational scalar multiple of the
circle's image in the rational quotient. -/
@[simp]
theorem circleTensorDetector_tmul (q : ℚ) (m : circleModule) :
    circleTensorDetector (q ⊗ₜ[ℤ] m) = q • AddCircle.toRationalQuotient m :=
  TensorProduct.rationalCircleDetector_tmul q m

/-- On a real representative, the detector sends `q ⊗ [x]` to the class of
`(q : ℝ) * x` modulo rational numbers. -/
@[simp]
theorem circleTensorDetector_tmul_coe (q : ℚ) (x : ℝ) :
    circleTensorDetector (q ⊗ₜ[ℤ] (x : AddCircle (1 : ℝ))) =
      (Submodule.span ℚ {(1 : ℝ)}).mkQ ((q : ℝ) * x) :=
  TensorProduct.rationalCircleDetector_tmul_coe q x

/-- Detecting the generator at coefficient `1` recovers the circle's descent to
real numbers modulo rationals. -/
theorem circleTensorDetector_generator (m : circleModule) :
    circleTensorDetector (circleTensorGenerator m) = AddCircle.toRationalQuotient m := by
  rw [circleTensorGenerator_apply, circleTensorDetector_tmul, one_smul]

/-- The linear composite of the detector with the incoming generator is the
integer-linear rational-quotient descent. -/
theorem circleTensorDetector_comp_generator :
    circleTensorDetector.comp circleTensorGenerator.toLinearMap =
      AddCircle.toRationalQuotient := by
  ext m
  exact circleTensorDetector_generator m

/-- The detector of the generator value at `[√2]` is the class of `√2` modulo
rationals. -/
theorem circleTensorDetector_irrationalGenerator :
    circleTensorDetector irrationalGenerator =
      (Submodule.span ℚ {(1 : ℝ)}).mkQ (Real.sqrt 2) := by
  rw [irrationalGenerator_eq_tmul]
  exact TensorProduct.rationalCircleDetector_one_tmul_coe (Real.sqrt 2)

/-- The algebraic detector has nonzero value on the generator at `[√2]`, by the
rational-quotient argument and irrationality of `√2`. -/
theorem circleTensorDetector_irrationalGenerator_ne_zero :
    circleTensorDetector irrationalGenerator ≠ 0 := by
  rw [irrationalGenerator_eq_tmul]
  exact TensorProduct.rationalCircleDetector_sqrt_two_ne_zero

/-- The generator at `[√2]` is nonzero in the circle tensor, as proved by the
algebraic rational-quotient detector. -/
theorem irrationalGenerator_ne_zero : irrationalGenerator ≠ 0 := by
  rw [irrationalGenerator_eq_tmul]
  exact TensorProduct.rationalCircle_tensor_sqrt_two_ne_zero

/-- The incoming generator at coefficient `1` kills every rational angle. -/
theorem circleTensorGenerator_rationalAngle (q : ℚ) :
    circleTensorGenerator (AddCircle.rationalAngle q) = 0 :=
  TopModuleCat.tensorGenerator_rationalAngle (1 : ℚ) q

/-- The half-angle is nonzero in the circle, since its real representative lies
strictly between `0` and the period `1`. -/
theorem rationalHalf_ne_zero : AddCircle.rationalAngle (1 / 2 : ℚ) ≠ 0 := by
  let _ : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  rw [AddCircle.rationalAngle_apply, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
  intro h
  have hzero : (1 / 2 : ℝ) = 0 :=
    (AddCircle.coe_eq_zero_iff_of_mem_Ico
      (show (1 / 2 : ℝ) ∈ Set.Ico 0 (1 : ℝ) from
        ⟨one_half_pos.le, one_half_lt_one⟩)).mp h
  exact (ne_of_gt (one_half_pos : (0 : ℝ) < 1 / 2)) hzero

/-- Integer angles are already zero in the circle. The half-angle instead is
nonzero, has its positive denominator as an integer annihilator, and maps to zero
under the tensor generator. -/
theorem rationalAngle_boundaries :
    (∀ n : ℤ, AddCircle.rationalAngle (n : ℚ) = 0) ∧
      AddCircle.rationalAngle (1 / 2 : ℚ) ≠ 0 ∧
      0 < ((1 / 2 : ℚ).den : ℤ) ∧
      ((1 / 2 : ℚ).den : ℤ) • AddCircle.rationalAngle (1 / 2 : ℚ) = 0 ∧
      circleTensorGenerator (AddCircle.rationalAngle (1 / 2 : ℚ)) = 0 :=
  ⟨AddCircle.rationalAngle_intCast, rationalHalf_ne_zero,
    Nat.cast_pos.mpr (Rat.pos (1 / 2 : ℚ)),
    AddCircle.den_zsmul_rationalAngle (1 / 2 : ℚ),
    circleTensorGenerator_rationalAngle (1 / 2 : ℚ)⟩

/-- The rational-circle model has flat coefficients, a compact Hausdorff right
factor with jointly continuous integer action, and its canonical continuous tensor
generator. All rational angles are dense and killed by every rational pure tensor,
while the algebraic detector distinguishes the generator at `[√2]` from zero. -/
theorem rationalCircle_properties :
    Module.Flat ℤ rationalCoefficients ∧
      ContinuousSMul ℤ circleModule ∧
      T2Space circleModule ∧
      CompactSpace circleModule ∧
      (rationalCircleTensor : Type) = TensorProduct ℤ ℚ (AddCircle (1 : ℝ)) ∧
      Continuous circleTensorGenerator ∧
      (∀ m : circleModule, circleTensorGenerator m = (1 : ℚ) ⊗ₜ[ℤ] m) ∧
      DenseRange (AddCircle.rationalAngle : ℚ → circleModule) ∧
      (∀ c q : ℚ,
        (c ⊗ₜ[ℤ] AddCircle.rationalAngle q : rationalCircleTensor) = 0) ∧
      (∀ q : ℚ, circleTensorGenerator (AddCircle.rationalAngle q) = 0) ∧
      circleTensorDetector irrationalGenerator ≠ 0 ∧
      irrationalGenerator ≠ 0 :=
  ⟨rationalCoefficients_flat, circleModule_continuousSMul, circleModule_t2,
    circleModule_compact, rationalCircleTensor_coe, circleTensorGenerator_continuous,
    circleTensorGenerator_apply, AddCircle.denseRange_rationalAngle,
    TensorProduct.tmul_rationalAngle_eq_zero, circleTensorGenerator_rationalAngle,
    circleTensorDetector_irrationalGenerator_ne_zero, irrationalGenerator_ne_zero⟩

/-- The integer tensor of rational coefficients with the usual real circle is not
Hausdorff for the finest topological-module topology of `TopModuleCat.tensorLeftObj`.
Thus flat rational coefficients do not preserve Hausdorffness, even when the circle
is compact Hausdorff and its integer action is jointly continuous.

This is the rational-circle conclusion of the proof route credited above to
Formal Frontier Agents (Lantern), using the cited circle, rational-angle and
algebraic detector APIs and their Mathlib foundations. -/
theorem not_t2Space_rationalCircleTensor : ¬ T2Space rationalCircleTensor := by
  intro h
  let : T2Space rationalCircleTensor := h
  have hzero : (circleTensorGenerator : circleModule → rationalCircleTensor) =
      fun _ ↦ 0 := by
    apply Continuous.ext_on AddCircle.denseRange_rationalAngle
      circleTensorGenerator_continuous continuous_const
    rintro _ ⟨q, rfl⟩
    exact circleTensorGenerator_rationalAngle q
  apply irrationalGenerator_ne_zero
  calc
    irrationalGenerator =
        circleTensorGenerator ((Real.sqrt 2 : ℝ) : AddCircle (1 : ℝ)) := by
      rw [irrationalGenerator_eq_tmul, circleTensorGenerator_apply]
    _ = 0 := congrFun hzero _

end TensorCircleExamples
