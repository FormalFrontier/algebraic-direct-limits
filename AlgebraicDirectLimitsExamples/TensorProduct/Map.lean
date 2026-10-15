/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicDirectLimits.Topology.TensorProduct
public import AlgebraicDirectLimitsExamples.ProjectiveTensorSeparation
public import Mathlib.LinearAlgebra.Finsupp.Defs

/-!
# Linearity of continuous tensor maps

Whole continuous-map equalities distribute coefficient projections and right-factor
maps over addition, integer scaling and finite sums. The concrete coefficients are
`ℕ →₀ ℤ`, with no coefficient topology; the right module is the usual nondiscrete
real module. The data and continuous product-coordinate detector are reused from
`ProjectiveTensorSeparationExamples`.

The projections onto positions zero and one send the tensor `(e₀ + e₁) ⊗ 1` to
independently supported nonzero tensors. Their sum has coordinates `(1, 1)`, while
weighting the projections by two and three gives coordinates `(2, 3)`. The detector
has Pi codomain `ℕ → realModule`, not a finitely supported codomain. Finite support
of these particular outputs is not a hypothesis on the generic tensor-map laws.

The bundled operator `TopModuleCat.tensorMapBilinear` is also used on the standard
integer module. Mathlib's algebraic left unitor detects `1 ⊗ 1` as `1`, the
identity value is nonzero, and scaling the two input maps by `2` and `3` gives
detected value `6`. The weighted calculation uses the bundle's linear-map API.

## References

The one-sided tensor topology follows the Continuous Group Cohomology formalization
by Formal Frontier Agents, including Beacon's original development. The algebraic
map-variable laws, bilinear-map constructors and algebraic tensor unitor are
Mathlib's APIs by Kenny Lau and Mario Carneiro;
Finsupp linear projections and inclusions are due to Johannes Hölzl and the authors
credited in the reused tensor-separation examples. No second tensor-map construction
is used here.
-/

@[expose] public section

open scoped TensorProduct
open ProjectiveTensorSeparationExamples

universe uR uC uD uM uN

namespace TensorMapExamples

/-- The algebraic projection onto one finitely supported integer coordinate. -/
noncomputable def coefficientProjection (n : ℕ) :
    infiniteCoefficients →ₗ[ℤ] infiniteCoefficients :=
  (Finsupp.lsingle n : ℤ →ₗ[ℤ] infiniteCoefficients).comp
    (Finsupp.lapply n : infiniteCoefficients →ₗ[ℤ] ℤ)

/-- Tensor the coefficient projection with the continuous identity on the usual reals. -/
noncomputable abbrev tensorProjection (n : ℕ) : infiniteTensor →L[ℤ] infiniteTensor :=
  TopModuleCat.tensorMapCLM ℤ (coefficientProjection n)
    (ContinuousLinearMap.id ℤ realModule)

/-- A tensor involving two independent coefficient positions with right value one. -/
noncomputable def twoCoordinateInput : infiniteTensor :=
  (integerBasisVector 0 + integerBasisVector 1) ⊗ₜ[ℤ] (1 : realModule)

/-- Retain the first two coefficient coordinates while leaving the right factor unchanged. -/
noncomputable abbrev twoCoordinateMap : infiniteTensor →L[ℤ] infiniteTensor :=
  TopModuleCat.tensorMapCLM ℤ (coefficientProjection 0 + coefficientProjection 1)
    (ContinuousLinearMap.id ℤ realModule)

/-- Zero in either factor gives the zero endomorphism of the concrete tensor model. -/
theorem projectionTensor_zero :
    TopModuleCat.tensorMapCLM ℤ (0 : infiniteCoefficients →ₗ[ℤ] infiniteCoefficients)
        (ContinuousLinearMap.id ℤ realModule) = (0 : infiniteTensor →L[ℤ] infiniteTensor) ∧
      TopModuleCat.tensorMapCLM ℤ (coefficientProjection 0)
        (0 : realModule →L[ℤ] realModule) = (0 : infiniteTensor →L[ℤ] infiniteTensor) := by
  exact ⟨TopModuleCat.tensorMapCLM_zero_left ℤ
    (C := infiniteCoefficients) (D := infiniteCoefficients)
    (M := realModule) (N := realModule) (ContinuousLinearMap.id ℤ realModule),
    TopModuleCat.tensorMapCLM_zero_right ℤ
      (C := infiniteCoefficients) (D := infiniteCoefficients)
      (M := realModule) (N := realModule) (coefficientProjection 0)⟩

/-- The sum of the two algebraic projections is the sum of whole continuous tensor maps. -/
theorem twoCoordinateMap_eq_add :
    twoCoordinateMap = tensorProjection 0 + tensorProjection 1 := by
  exact TopModuleCat.tensorMapCLM_add_left ℤ
    (C := infiniteCoefficients) (D := infiniteCoefficients)
    (M := realModule) (N := realModule) (coefficientProjection 0)
    (coefficientProjection 1) (ContinuousLinearMap.id ℤ realModule)

/-- Unequal weights on the two coefficient projections distribute at the whole-map level. -/
theorem weightedProjectionTensor_eq :
    TopModuleCat.tensorMapCLM ℤ
        ((2 : ℤ) • coefficientProjection 0 + (3 : ℤ) • coefficientProjection 1)
        (ContinuousLinearMap.id ℤ realModule) =
      (2 : ℤ) • tensorProjection 0 + (3 : ℤ) • tensorProjection 1 := by
  change TopModuleCat.tensorMapCLM ℤ
      (C := infiniteCoefficients) (D := infiniteCoefficients)
      (M := realModule) (N := realModule)
      ((2 : ℤ) • coefficientProjection 0 + (3 : ℤ) • coefficientProjection 1)
      (ContinuousLinearMap.id ℤ realModule) =
    (2 : ℤ) • TopModuleCat.tensorMapCLM ℤ
        (C := infiniteCoefficients) (D := infiniteCoefficients)
        (M := realModule) (N := realModule) (coefficientProjection 0)
        (ContinuousLinearMap.id ℤ realModule) +
      (3 : ℤ) • TopModuleCat.tensorMapCLM ℤ
        (C := infiniteCoefficients) (D := infiniteCoefficients)
        (M := realModule) (N := realModule) (coefficientProjection 1)
        (ContinuousLinearMap.id ℤ realModule)
  rw [TopModuleCat.tensorMapCLM_add_left ℤ
    (C := infiniteCoefficients) (D := infiniteCoefficients)
    (M := realModule) (N := realModule) ((2 : ℤ) • coefficientProjection 0)
    ((3 : ℤ) • coefficientProjection 1) (ContinuousLinearMap.id ℤ realModule)]
  exact congrArg₂ (fun f g : infiniteTensor →L[ℤ] infiniteTensor ↦ f + g)
    (TopModuleCat.tensorMapCLM_smul_left ℤ
      (C := infiniteCoefficients) (D := infiniteCoefficients)
      (M := realModule) (N := realModule) (2 : ℤ) (coefficientProjection 0)
      (ContinuousLinearMap.id ℤ realModule))
    (TopModuleCat.tensorMapCLM_smul_left ℤ
      (C := infiniteCoefficients) (D := infiniteCoefficients)
      (M := realModule) (N := realModule) (3 : ℤ) (coefficientProjection 1)
      (ContinuousLinearMap.id ℤ realModule))

/-- Any finite collection of coefficient projections distributes as continuous tensor maps. -/
theorem tensorProjection_sum (s : Finset ℕ) :
    TopModuleCat.tensorMapCLM ℤ (∑ n ∈ s, coefficientProjection n)
        (ContinuousLinearMap.id ℤ realModule) = ∑ n ∈ s, tensorProjection n := by
  exact TopModuleCat.tensorMapCLM_sum_left ℤ
    (C := infiniteCoefficients) (D := infiniteCoefficients)
    (M := realModule) (N := realModule) s coefficientProjection
    (ContinuousLinearMap.id ℤ realModule)

/-- A two-term weighted sum on the right factor distributes without changing coefficients. -/
theorem twoCoordinateMap_weighted_right :
    TopModuleCat.tensorMapCLM ℤ (coefficientProjection 0 + coefficientProjection 1)
        ((2 : ℤ) • ContinuousLinearMap.id ℤ realModule +
          (3 : ℤ) • ContinuousLinearMap.id ℤ realModule) =
      (2 : ℤ) • twoCoordinateMap + (3 : ℤ) • twoCoordinateMap := by
  change TopModuleCat.tensorMapCLM ℤ
      (C := infiniteCoefficients) (D := infiniteCoefficients)
      (M := realModule) (N := realModule) (coefficientProjection 0 + coefficientProjection 1)
      ((2 : ℤ) • ContinuousLinearMap.id ℤ realModule +
        (3 : ℤ) • ContinuousLinearMap.id ℤ realModule) =
    (2 : ℤ) • TopModuleCat.tensorMapCLM ℤ
        (C := infiniteCoefficients) (D := infiniteCoefficients)
        (M := realModule) (N := realModule) (coefficientProjection 0 + coefficientProjection 1)
        (ContinuousLinearMap.id ℤ realModule) +
      (3 : ℤ) • TopModuleCat.tensorMapCLM ℤ
        (C := infiniteCoefficients) (D := infiniteCoefficients)
        (M := realModule) (N := realModule) (coefficientProjection 0 + coefficientProjection 1)
        (ContinuousLinearMap.id ℤ realModule)
  rw [TopModuleCat.tensorMapCLM_add_right ℤ
    (C := infiniteCoefficients) (D := infiniteCoefficients)
    (M := realModule) (N := realModule) (coefficientProjection 0 + coefficientProjection 1)
    ((2 : ℤ) • ContinuousLinearMap.id ℤ realModule)
    ((3 : ℤ) • ContinuousLinearMap.id ℤ realModule)]
  exact congrArg₂ (fun f g : infiniteTensor →L[ℤ] infiniteTensor ↦ f + g)
    (TopModuleCat.tensorMapCLM_smul_right ℤ
      (C := infiniteCoefficients) (D := infiniteCoefficients)
      (M := realModule) (N := realModule) (2 : ℤ)
      (coefficientProjection 0 + coefficientProjection 1) (ContinuousLinearMap.id ℤ realModule))
    (TopModuleCat.tensorMapCLM_smul_right ℤ
      (C := infiniteCoefficients) (D := infiniteCoefficients)
      (M := realModule) (N := realModule) (3 : ℤ)
      (coefficientProjection 0 + coefficientProjection 1) (ContinuousLinearMap.id ℤ realModule))

/-- Finite sums of weighted real identities distribute as whole continuous tensor maps. -/
theorem twoCoordinateMap_sum_right (s : Finset ℕ) (r : ℕ → ℤ) :
    TopModuleCat.tensorMapCLM ℤ (coefficientProjection 0 + coefficientProjection 1)
        (∑ n ∈ s, r n • ContinuousLinearMap.id ℤ realModule) =
      ∑ n ∈ s, r n • twoCoordinateMap := by
  change TopModuleCat.tensorMapCLM ℤ
      (C := infiniteCoefficients) (D := infiniteCoefficients)
      (M := realModule) (N := realModule) (coefficientProjection 0 + coefficientProjection 1)
      (∑ n ∈ s, r n • ContinuousLinearMap.id ℤ realModule) =
    ∑ n ∈ s, r n • TopModuleCat.tensorMapCLM ℤ
      (C := infiniteCoefficients) (D := infiniteCoefficients)
      (M := realModule) (N := realModule) (coefficientProjection 0 + coefficientProjection 1)
      (ContinuousLinearMap.id ℤ realModule)
  rw [TopModuleCat.tensorMapCLM_sum_right ℤ
    (C := infiniteCoefficients) (D := infiniteCoefficients)
    (M := realModule) (N := realModule) s (coefficientProjection 0 + coefficientProjection 1)
    (fun n ↦ r n • ContinuousLinearMap.id ℤ realModule)]
  refine Finset.sum_congr rfl ?_
  intro n _
  exact TopModuleCat.tensorMapCLM_smul_right ℤ
    (C := infiniteCoefficients) (D := infiniteCoefficients)
    (M := realModule) (N := realModule) (r n)
    (coefficientProjection 0 + coefficientProjection 1) (ContinuousLinearMap.id ℤ realModule)

/-- The whole-map addition law applies to every input, not just pure tensors. -/
theorem twoCoordinateMap_apply (x : infiniteTensor) :
    twoCoordinateMap x = tensorProjection 0 x + tensorProjection 1 x := by
  simpa only [add_apply] using DFunLike.congr_fun twoCoordinateMap_eq_add x

/-- The two projections recover the two distinct pure-tensor summands of the exhibited input. -/
theorem tensorProjection_input :
    tensorProjection 0 twoCoordinateInput = infiniteFirstTensor ∧
      tensorProjection 1 twoCoordinateInput =
        (show infiniteTensor from integerBasisVector 1 ⊗ₜ[ℤ] (1 : realModule)) := by
  have h₀ : coefficientProjection 0 (integerBasisVector 0 + integerBasisVector 1) =
      integerBasisVector 0 := by
    simp [coefficientProjection, integerBasisVector]
  have h₁ : coefficientProjection 1 (integerBasisVector 0 + integerBasisVector 1) =
      integerBasisVector 1 := by
    simp [coefficientProjection, integerBasisVector]
  constructor
  · change TopModuleCat.tensorMapCLM ℤ (coefficientProjection 0)
      (ContinuousLinearMap.id ℤ realModule)
      ((integerBasisVector 0 + integerBasisVector 1) ⊗ₜ[ℤ] (1 : realModule)) =
        integerBasisVector 0 ⊗ₜ[ℤ] (1 : realModule)
    rw [TopModuleCat.tensorMapCLM_tmul, h₀, ContinuousLinearMap.id_apply]
  · change TopModuleCat.tensorMapCLM ℤ (coefficientProjection 1)
      (ContinuousLinearMap.id ℤ realModule)
      ((integerBasisVector 0 + integerBasisVector 1) ⊗ₜ[ℤ] (1 : realModule)) =
        integerBasisVector 1 ⊗ₜ[ℤ] (1 : realModule)
    rw [TopModuleCat.tensorMapCLM_tmul, h₁, ContinuousLinearMap.id_apply]

/-- Product coordinates show that the projected outputs have disjoint single-coordinate support. -/
theorem tensorProjection_input_coordinates (n i : ℕ) :
    infiniteCoordinates (tensorProjection n twoCoordinateInput) i =
      if (n = 0 ∨ n = 1) ∧ n = i then (1 : realModule) else 0 := by
  by_cases h₀ : n = 0
  · subst n
    rw [tensorProjection_input.1]
    change infiniteCoordinates (integerBasisVector 0 ⊗ₜ[ℤ] (1 : realModule)) i = _
    simpa using infiniteCoordinates_basis_tmul 0 i (1 : realModule)
  · by_cases h₁ : n = 1
    · subst n
      rw [tensorProjection_input.2]
      simpa using infiniteCoordinates_basis_tmul 1 i (1 : realModule)
    · have hcoeff : coefficientProjection n
          (integerBasisVector 0 + integerBasisVector 1) = 0 := by
        simp [coefficientProjection, integerBasisVector, h₀, h₁]
      have hmap : tensorProjection n twoCoordinateInput = 0 := by
        change TopModuleCat.tensorMapCLM ℤ
            (C := infiniteCoefficients) (D := infiniteCoefficients)
            (M := realModule) (N := realModule) (coefficientProjection n)
            (ContinuousLinearMap.id ℤ realModule)
            ((integerBasisVector 0 + integerBasisVector 1) ⊗ₜ[ℤ] (1 : realModule)) =
          (0 : TopModuleCat.tensorLeftObj ℤ infiniteCoefficients realModule)
        rw [TopModuleCat.tensorMapCLM_tmul ℤ
          (C := infiniteCoefficients) (D := infiniteCoefficients)
          (M := realModule) (N := realModule) (coefficientProjection n)
          (ContinuousLinearMap.id ℤ realModule)
          (integerBasisVector 0 + integerBasisVector 1) (1 : realModule),
          hcoeff, ContinuousLinearMap.id_apply, TensorProduct.zero_tmul]
        rfl
      calc
        infiniteCoordinates (tensorProjection n twoCoordinateInput) i =
            infiniteCoordinates (0 : infiniteTensor) i :=
          congrArg (fun x : infiniteTensor ↦ infiniteCoordinates x i) hmap
        _ = 0 := congrFun infiniteCoordinates.map_zero i
        _ = _ := by simp [h₀, h₁]

/-- The sum retains value one at both coefficient positions and vanishes elsewhere. -/
theorem twoCoordinateMap_input_coordinates (i : ℕ) :
    infiniteCoordinates (twoCoordinateMap twoCoordinateInput) i =
      if i = 0 ∨ i = 1 then (1 : realModule) else 0 := by
  rw [twoCoordinateMap_apply]
  calc
    infiniteCoordinates
        (tensorProjection 0 twoCoordinateInput + tensorProjection 1 twoCoordinateInput) i =
        (if ((0 : ℕ) = 0 ∨ (0 : ℕ) = 1) ∧ (0 : ℕ) = i then (1 : realModule) else 0) +
          (if ((1 : ℕ) = 0 ∨ (1 : ℕ) = 1) ∧ (1 : ℕ) = i then (1 : realModule) else 0) :=
      (congrFun (infiniteCoordinates.map_add
        (tensorProjection 0 twoCoordinateInput) (tensorProjection 1 twoCoordinateInput)) i).trans
          (congrArg₂ (fun x y : realModule ↦ x + y)
            (tensorProjection_input_coordinates 0 i) (tensorProjection_input_coordinates 1 i))
    _ = _ := by
      by_cases h₀ : i = 0
      · subst i
        norm_num
      · by_cases h₁ : i = 1
        · subst i
          norm_num
        · simp [h₀, h₁, Ne.symm h₀, Ne.symm h₁]

/-- The input and both terms are nonzero, the terms are distinct, and their sum is nonzero. -/
theorem tensorProjection_input_nonzero :
    twoCoordinateInput ≠ 0 ∧
      tensorProjection 0 twoCoordinateInput ≠ 0 ∧
      tensorProjection 1 twoCoordinateInput ≠ 0 ∧
      tensorProjection 0 twoCoordinateInput ≠ tensorProjection 1 twoCoordinateInput ∧
      twoCoordinateMap twoCoordinateInput ≠ 0 := by
  have hzero (i : ℕ) : infiniteCoordinates (0 : infiniteTensor) i = (0 : realModule) :=
    congrFun infiniteCoordinates.map_zero i
  have hinput : infiniteCoordinates twoCoordinateInput 0 = 1 := by
    change infiniteCoordinates
      ((integerBasisVector 0 + integerBasisVector 1) ⊗ₜ[ℤ] (1 : realModule)) 0 = 1
    rw [TensorProduct.add_tmul]
    exact (congrFun (infiniteCoordinates.map_add
      (show infiniteTensor from integerBasisVector 0 ⊗ₜ[ℤ] (1 : realModule))
      (show infiniteTensor from integerBasisVector 1 ⊗ₜ[ℤ] (1 : realModule))) 0).trans
        (by norm_num [infiniteCoordinates_basis_tmul])
  have h₀₀ : infiniteCoordinates (tensorProjection 0 twoCoordinateInput) 0 = 1 := by
    simpa using tensorProjection_input_coordinates 0 0
  have h₁₁ : infiniteCoordinates (tensorProjection 1 twoCoordinateInput) 1 = 1 := by
    simpa using tensorProjection_input_coordinates 1 1
  have h₁₀ : infiniteCoordinates (tensorProjection 1 twoCoordinateInput) 0 = 0 := by
    simpa using tensorProjection_input_coordinates 1 0
  have hsum : infiniteCoordinates (twoCoordinateMap twoCoordinateInput) 0 = 1 := by
    simpa using twoCoordinateMap_input_coordinates 0
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h
    apply (one_ne_zero : (1 : ℝ) ≠ 0)
    have he := congrArg (fun x : infiniteTensor ↦ infiniteCoordinates x 0) h
    rw [hinput, hzero] at he
    exact he
  · intro h
    apply (one_ne_zero : (1 : ℝ) ≠ 0)
    have he := congrArg (fun x : infiniteTensor ↦ infiniteCoordinates x 0) h
    rw [h₀₀, hzero] at he
    exact he
  · intro h
    apply (one_ne_zero : (1 : ℝ) ≠ 0)
    have he := congrArg (fun x : infiniteTensor ↦ infiniteCoordinates x 1) h
    rw [h₁₁, hzero] at he
    exact he
  · intro h
    apply (one_ne_zero : (1 : ℝ) ≠ 0)
    have he := congrArg (fun x : infiniteTensor ↦ infiniteCoordinates x 0) h
    rw [h₀₀, h₁₀] at he
    exact he
  · intro h
    apply (one_ne_zero : (1 : ℝ) ≠ 0)
    have he := congrArg (fun x : infiniteTensor ↦ infiniteCoordinates x 0) h
    rw [hsum, hzero] at he
    exact he

/-- The finite-sum law retains both independently supported terms of the concrete input. -/
theorem twoCoordinateMap_input_sum :
    twoCoordinateMap twoCoordinateInput =
      ∑ n ∈ ({0, 1} : Finset ℕ), tensorProjection n twoCoordinateInput := by
  rw [Finset.sum_pair (show (0 : ℕ) ≠ 1 from Nat.zero_ne_one)]
  exact twoCoordinateMap_apply twoCoordinateInput

/-- Unequal coefficient weights are visible in the two real output coordinates. -/
theorem weightedProjectionTensor_input_coordinates :
    infiniteCoordinates
        (TopModuleCat.tensorMapCLM ℤ
          ((2 : ℤ) • coefficientProjection 0 + (3 : ℤ) • coefficientProjection 1)
          (ContinuousLinearMap.id ℤ realModule) twoCoordinateInput) 0 = 2 ∧
      infiniteCoordinates
        (TopModuleCat.tensorMapCLM ℤ
          ((2 : ℤ) • coefficientProjection 0 + (3 : ℤ) • coefficientProjection 1)
          (ContinuousLinearMap.id ℤ realModule) twoCoordinateInput) 1 = 3 := by
  have hcoord (i : ℕ) :
      infiniteCoordinates
          (TopModuleCat.tensorMapCLM ℤ
            ((2 : ℤ) • coefficientProjection 0 + (3 : ℤ) • coefficientProjection 1)
            (ContinuousLinearMap.id ℤ realModule) twoCoordinateInput) i =
        (2 : ℤ) • infiniteCoordinates (tensorProjection 0 twoCoordinateInput) i +
          (3 : ℤ) • infiniteCoordinates (tensorProjection 1 twoCoordinateInput) i := by
    rw [weightedProjectionTensor_eq]
    change infiniteCoordinates
      ((2 : ℤ) • tensorProjection 0 twoCoordinateInput +
        (3 : ℤ) • tensorProjection 1 twoCoordinateInput) i = _
    exact (congrFun (infiniteCoordinates.map_add
      ((2 : ℤ) • tensorProjection 0 twoCoordinateInput)
      ((3 : ℤ) • tensorProjection 1 twoCoordinateInput)) i).trans
        (congrArg₂ (fun x y : realModule ↦ x + y)
          (congrFun (infiniteCoordinates.map_smul (2 : ℤ)
            (tensorProjection 0 twoCoordinateInput)) i)
          (congrFun (infiniteCoordinates.map_smul (3 : ℤ)
            (tensorProjection 1 twoCoordinateInput)) i))
  constructor
  · exact (hcoord 0).trans (by norm_num [tensorProjection_input_coordinates])
  · exact (hcoord 1).trans (by norm_num [tensorProjection_input_coordinates])

/-- Integers with their usual algebraic module data, without coefficient topology. -/
abbrev integerCoefficients : ModuleCat ℤ := ModuleCat.of ℤ ℤ

/-- The same integer module with its standard discrete topology. -/
noncomputable abbrev integerModule : TopModuleCat ℤ := TopModuleCat.of ℤ ℤ

/-- The canonical one-sided tensor of the standard integer modules. -/
noncomputable abbrev integerTensor : TopModuleCat ℤ :=
  TopModuleCat.tensorLeftObj ℤ integerCoefficients integerModule

/-- The bundled tensor-map operator on the standard integer modules. -/
noncomputable abbrev integerTensorMapBilinear :
    (integerCoefficients →ₗ[ℤ] integerCoefficients) →ₗ[ℤ]
      (integerModule →L[ℤ] integerModule) →ₗ[ℤ] integerTensor →L[ℤ] integerTensor :=
  TopModuleCat.tensorMapBilinear ℤ
    integerCoefficients integerCoefficients integerModule integerModule

/-- The tensor of the two integer units. -/
noncomputable def integerUnitTensor : integerTensor :=
  (1 : integerCoefficients) ⊗ₜ[ℤ] (1 : integerModule)

/-- The algebraic left unitor detects the tensor of the units as one. -/
theorem integerUnitTensor_lid : TensorProduct.lid ℤ ℤ integerUnitTensor = 1 := by
  simp [integerUnitTensor]

/-- The standard integer tensor carrier is nonzero. -/
theorem integerUnitTensor_ne_zero : integerUnitTensor ≠ 0 := by
  intro h
  have he := integerUnitTensor_lid
  have hzero : TensorProduct.lid ℤ ℤ (0 : integerTensor) = 0 :=
    (TensorProduct.lid ℤ ℤ).map_zero
  rw [h] at he
  replace he := hzero.symm.trans he
  exact (one_ne_zero : (1 : ℤ) ≠ 0) he.symm

/-- Scaling both input maps is visible through the bundle's linear-map API. -/
theorem integerTensorMapBilinear_weighted (a b : ℤ) :
    TensorProduct.lid ℤ ℤ
      (integerTensorMapBilinear
        (a • (LinearMap.id : integerCoefficients →ₗ[ℤ] integerCoefficients))
        (b • ContinuousLinearMap.id ℤ integerModule) integerUnitTensor) = a * b := by
  let I : integerCoefficients →ₗ[ℤ] integerCoefficients := LinearMap.id
  let J : integerModule →L[ℤ] integerModule := ContinuousLinearMap.id ℤ integerModule
  let τ : integerCoefficients → integerModule → integerTensor := fun c m ↦ c ⊗ₜ[ℤ] m
  let lidE : integerTensor → ℤ := fun x ↦ TensorProduct.lid ℤ ℤ x
  have ht : integerTensorMapBilinear (a • I) (b • J) integerUnitTensor =
      τ ((a • I) (1 : integerCoefficients)) ((b • J) (1 : integerModule)) :=
    TopModuleCat.tensorMapBilinear_tmul ℤ (a • I) (b • J)
      (1 : integerCoefficients) (1 : integerModule)
  have ha : (a • I) (1 : integerCoefficients) = (a : integerCoefficients) := by
    calc
      _ = integerCoefficients.isModule.smul a (1 : integerCoefficients) :=
        LinearMap.smul_apply a I (1 : integerCoefficients)
      _ = a := by
        simpa only [Int.zsmul_eq_mul, mul_one] using
          int_smul_eq_zsmul integerCoefficients.isModule a (1 : integerCoefficients)
  have hb : (b • J) (1 : integerModule) = (b : integerModule) := by
    calc
      _ = integerModule.toModuleCat.isModule.smul b (1 : integerModule) :=
        smul_apply J b (1 : integerModule)
      _ = b := by
        simpa only [Int.zsmul_eq_mul, mul_one] using
          int_smul_eq_zsmul integerModule.toModuleCat.isModule b (1 : integerModule)
  calc
    _ = lidE (τ (a : integerCoefficients) (b : integerModule)) :=
      congrArg lidE (ht.trans (congrArg₂ τ ha hb))
    _ = a * b := by
      simpa only [lidE, τ, smul_eq_mul] using
        (TensorProduct.lid_tmul (R := ℤ) (M := ℤ) b a)

/-- Neither the identity value nor the whole integer bilinear operator is zero. -/
theorem integerTensorMapBilinear_id_nonzero :
    integerTensorMapBilinear LinearMap.id (ContinuousLinearMap.id ℤ integerModule) ≠ 0 ∧
      integerTensorMapBilinear ≠ 0 := by
  have hdet : TensorProduct.lid ℤ ℤ
      (integerTensorMapBilinear LinearMap.id
        (ContinuousLinearMap.id ℤ integerModule) integerUnitTensor) = 1 := by
    simpa only [one_smul, one_mul] using integerTensorMapBilinear_weighted 1 1
  have hmap : integerTensorMapBilinear LinearMap.id
      (ContinuousLinearMap.id ℤ integerModule) ≠ 0 := by
    intro h
    have hzero : TensorProduct.lid ℤ ℤ (0 : integerTensor) = 0 :=
      (TensorProduct.lid ℤ ℤ).map_zero
    rw [h, zero_apply] at hdet
    replace hdet := hzero.symm.trans hdet
    exact (one_ne_zero : (1 : ℤ) ≠ 0) hdet.symm
  refine ⟨hmap, ?_⟩
  intro h
  apply hmap
  have he := DFunLike.congr_fun
    (DFunLike.congr_fun h (LinearMap.id : integerCoefficients →ₗ[ℤ] integerCoefficients))
    (ContinuousLinearMap.id ℤ integerModule)
  simpa only [LinearMap.zero_apply] using he

/-- The two independently weighted maps give a tensor detected as six, not zero. -/
theorem integerTensorMapBilinear_weighted_nonzero :
    TensorProduct.lid ℤ ℤ
        (integerTensorMapBilinear
          ((2 : ℤ) • (LinearMap.id : integerCoefficients →ₗ[ℤ] integerCoefficients))
          ((3 : ℤ) • ContinuousLinearMap.id ℤ integerModule) integerUnitTensor) = 6 ∧
      integerTensorMapBilinear
        ((2 : ℤ) • (LinearMap.id : integerCoefficients →ₗ[ℤ] integerCoefficients))
        ((3 : ℤ) • ContinuousLinearMap.id ℤ integerModule) integerUnitTensor ≠ 0 := by
  have hdet := (integerTensorMapBilinear_weighted 2 3).trans
    (show (2 : ℤ) * 3 = 6 by norm_num)
  refine ⟨hdet, ?_⟩
  intro h
  have hzero : TensorProduct.lid ℤ ℤ (0 : integerTensor) = 0 :=
    (TensorProduct.lid ℤ ℤ).map_zero
  rw [h] at hdet
  replace hdet := hzero.symm.trans hdet
  norm_num at hdet

section IndependentUniverses

variable (R : Type uR) [CommRing R] [TopologicalSpace R]
variable {C : ModuleCat.{uC} R} {D : ModuleCat.{uD} R}
variable {M : TopModuleCat.{uM} R} {N : TopModuleCat.{uN} R}

/-- Combining two weighted coefficient maps and two right maps distributes on an arbitrary tensor.
The factor carriers remain independently leveled and no coefficient topology is supplied. -/
theorem tensorMap_weighted_pair_apply (a b : R) (f₀ f₁ : C →ₗ[R] D)
    (g₀ g₁ : M →L[R] N) (x : TopModuleCat.tensorLeftObj R C M) :
    TopModuleCat.tensorMapCLM R (a • f₀ + b • f₁) (g₀ + g₁) x =
      a • (TopModuleCat.tensorMapCLM R f₀ g₀ x + TopModuleCat.tensorMapCLM R f₀ g₁ x) +
        b • (TopModuleCat.tensorMapCLM R f₁ g₀ x + TopModuleCat.tensorMapCLM R f₁ g₁ x) := by
  simp only [TopModuleCat.tensorMapCLM_add_left, TopModuleCat.tensorMapCLM_smul_left,
    TopModuleCat.tensorMapCLM_add_right, add_apply, smul_apply]
  rw [smul_add, smul_add]
  exact add_add_add_comm _ _ _ _

end IndependentUniverses

end TensorMapExamples
