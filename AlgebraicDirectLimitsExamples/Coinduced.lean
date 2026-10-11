/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicDirectLimits.Topology.Coinduced
public import Mathlib.LinearAlgebra.Prod

/-!
# Coinduced-module examples

The two coordinate injections generate a coinduced topology on a product module.
Addition is continuous from this topology over any ring. In particular, the
linearity of addition does not require commutativity of the scalar ring.

For the two integer axes in `ℤ × ℤ`, the functional `(x, y) ↦ x + 2 * y` is
continuous by the generator criterion. It takes the values `1` and `2` on the
respective unit generators and is a nonzero continuous linear map.
-/

@[expose] public section

universe uR uM

open CategoryTheory

namespace AlgebraicDirectLimitsExamples.Coinduced

variable {R : Type uR} [Ring R] [TopologicalSpace R]

/-- The two coordinate injections into the product of a module with itself. -/
def axisFamily (M : TopModuleCat.{uM} R) :
    ∀ _ : Bool, M.toModuleCat ⟶ ModuleCat.of R (M × M)
  | false => ModuleCat.ofHom (LinearMap.inl R M M)
  | true => ModuleCat.ofHom (LinearMap.inr R M M)

/-- The first generating map is the first coordinate injection. -/
@[simp]
theorem axisFamily_false_apply (M : TopModuleCat.{uM} R) (x : M) :
    axisFamily M false x = (x, 0) := rfl

/-- The second generating map is the second coordinate injection. -/
@[simp]
theorem axisFamily_true_apply (M : TopModuleCat.{uM} R) (x : M) :
    axisFamily M true x = (0, x) := rfl

/-- The product module with the topology coinduced by its two coordinate injections. -/
def axisModule (M : TopModuleCat.{uM} R) : TopModuleCat.{uM} R :=
  TopModuleCat.coinduced (axisFamily M)

/-- Addition on the product as a linear map, valid over a possibly noncommutative ring. -/
def sumMap (M : TopModuleCat.{uM} R) : axisModule M →ₗ[R] M :=
  (LinearMap.id : M →ₗ[R] M).coprod LinearMap.id

/-- The addition map sums the two coordinates. -/
@[simp]
theorem sumMap_apply (M : TopModuleCat.{uM} R) (p : axisModule M) :
    sumMap M p = p.1 + p.2 := rfl

/-- Addition composed with either coordinate injection is the identity. -/
@[simp]
theorem sumMap_axisFamily_apply (M : TopModuleCat.{uM} R) (i : Bool) (x : M) :
    sumMap M (axisFamily M i x) = x := by
  cases i
  · change x + 0 = x
    exact add_zero x
  · change 0 + x = x
    exact zero_add x

/-- Addition is continuous because both generating composites are the identity. -/
theorem sumMap_continuous (M : TopModuleCat.{uM} R) : Continuous (sumMap M) := by
  apply (TopModuleCat.continuous_coinduced_iff (axisFamily M) (sumMap M)).mpr
  intro i
  exact (continuous_id : Continuous (fun x : M ↦ x)).congr
    (fun x ↦ (sumMap_axisFamily_apply M i x).symm)

/-- The integer functional with weights one and two on the coordinate axes. -/
def integerFunctional : axisModule (TopModuleCat.of ℤ ℤ) →ₗ[ℤ] ℤ :=
  (LinearMap.id : ℤ →ₗ[ℤ] ℤ).coprod ((2 : ℤ) • LinearMap.id)

/-- The integer functional computes `x + 2 * y`. -/
@[simp]
theorem integerFunctional_apply (p : axisModule (TopModuleCat.of ℤ ℤ)) :
    integerFunctional p = p.1 + 2 * p.2 := rfl

/-- The integer functional restricts to the identity on the first coordinate axis. -/
@[simp]
theorem integerFunctional_axisFamily_false_apply (x : ℤ) :
    integerFunctional (axisFamily (TopModuleCat.of ℤ ℤ) false x) = x := by
  change x + 2 * 0 = x
  simp only [mul_zero, add_zero]

/-- The integer functional has weight two on the second coordinate axis. -/
@[simp]
theorem integerFunctional_axisFamily_true_apply (x : ℤ) :
    integerFunctional (axisFamily (TopModuleCat.of ℤ ℤ) true x) = 2 * x := by
  change 0 + 2 * x = 2 * x
  exact zero_add _

/-- Continuity of the weighted functional follows from its two generating composites. -/
theorem integerFunctional_continuous : Continuous integerFunctional := by
  apply (TopModuleCat.continuous_coinduced_iff (Y := TopModuleCat.of ℤ ℤ)
    (axisFamily (TopModuleCat.of ℤ ℤ)) integerFunctional).mpr
  intro i
  cases i
  · exact (continuous_id : Continuous (fun x : ℤ ↦ x)).congr
      (fun x ↦ (integerFunctional_axisFamily_false_apply x).symm)
  · exact (continuous_const.mul continuous_id :
      Continuous (fun x : ℤ ↦ (2 : ℤ) * x)).congr
      (fun x ↦ (integerFunctional_axisFamily_true_apply x).symm)

/-- The weighted integer functional bundled as a continuous linear map. -/
def integerFunctionalCLM : axisModule (TopModuleCat.of ℤ ℤ) →L[ℤ] ℤ :=
  ⟨integerFunctional, integerFunctional_continuous⟩

/-- The continuous linear map retains the weighted functional's formula. -/
@[simp]
theorem integerFunctionalCLM_apply (p : axisModule (TopModuleCat.of ℤ ℤ)) :
    integerFunctionalCLM p = p.1 + 2 * p.2 := integerFunctional_apply p

/-- The continuous linear map restricts to the identity on the first coordinate axis. -/
@[simp]
theorem integerFunctionalCLM_axisFamily_false_apply (x : ℤ) :
    integerFunctionalCLM (axisFamily (TopModuleCat.of ℤ ℤ) false x) = x := by
  change integerFunctional (axisFamily (TopModuleCat.of ℤ ℤ) false x) = x
  exact integerFunctional_axisFamily_false_apply x

/-- The continuous linear map has weight two on the second coordinate axis. -/
@[simp]
theorem integerFunctionalCLM_axisFamily_true_apply (x : ℤ) :
    integerFunctionalCLM (axisFamily (TopModuleCat.of ℤ ℤ) true x) = 2 * x := by
  change integerFunctional (axisFamily (TopModuleCat.of ℤ ℤ) true x) = 2 * x
  exact integerFunctional_axisFamily_true_apply x

/-- The first unit generator is detected by the continuous functional. -/
theorem integerFunctionalCLM_first_one :
    integerFunctionalCLM (axisFamily (TopModuleCat.of ℤ ℤ) false 1) = 1 := by
  exact integerFunctionalCLM_axisFamily_false_apply 1

/-- The second unit generator has weight two, rather than being killed. -/
theorem integerFunctionalCLM_second_one :
    integerFunctionalCLM (axisFamily (TopModuleCat.of ℤ ℤ) true 1) = 2 := by
  calc
    _ = (2 : ℤ) * 1 := integerFunctionalCLM_axisFamily_true_apply 1
    _ = 2 := mul_one _

/-- The continuous functional is nonzero, as witnessed on the first unit generator. -/
theorem integerFunctionalCLM_ne_zero : integerFunctionalCLM ≠ 0 := by
  intro h
  have hvalue : (1 : ℤ) = 0 := by
    calc
      (1 : ℤ) =
          integerFunctionalCLM (axisFamily (TopModuleCat.of ℤ ℤ) false 1) :=
        integerFunctionalCLM_first_one.symm
      _ = (0 : axisModule (TopModuleCat.of ℤ ℤ) →L[ℤ] ℤ)
          (axisFamily (TopModuleCat.of ℤ ℤ) false 1) :=
        DFunLike.congr_fun h _
      _ = 0 := zero_apply _
  exact one_ne_zero hvalue

end AlgebraicDirectLimitsExamples.Coinduced
