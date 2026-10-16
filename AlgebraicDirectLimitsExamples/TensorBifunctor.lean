/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicDirectLimits.Topology.TensorBifunctor
public import AlgebraicDirectLimitsExamples.TensorProduct.Map

/-!
# A weighted integer tensor map through the bifunctor

The standard uncurried tensor functor sends coefficient doubling and right-factor
tripling to a map whose value at `1 ⊗ 1` is detected as six by the algebraic left
unitor. The image is nonzero. This uses the existing integer model and weighted
bilinear-map calculation through the bifunctor's characteristic whole-map API.

The general construction asserts functoriality, not preservation of nonzero
tensors: empty coefficients and trivial rings already give zero tensors in
`TensorProductExamples.emptyCoefficient_tensor_eq_zero` and
`TensorProductExamples.trivialRing_tensor_eq_zero`.

## References

The integer tensor model, unitor detector and weighted calculation are those of
Formal Frontier Agents' `TensorMapExamples`, with its integer tensor models
and coinduced tensor topology. Mathlib supplies the algebraic tensor
map and unitor by Kenny Lau and Mario Carneiro and the functor currying
interface by Kim Morrison.
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct CategoryTheory.Prod

namespace TensorBifunctorExamples

local notation "Cℤ" => TensorMapExamples.integerCoefficients
local notation "Mℤ" => TensorMapExamples.integerModule
local notation "τ" => TensorMapExamples.integerUnitTensor

/-- Doubling on the standard algebraic integer coefficient module. -/
noncomputable def doubleCoefficients : Cℤ ⟶ Cℤ :=
  ConcreteCategory.ofHom (C := ModuleCat ℤ) (X := Cℤ) (Y := Cℤ)
    ((2 : ℤ) • (LinearMap.id : Cℤ →ₗ[ℤ] Cℤ))

/-- Tripling on the standard topological integer right module. -/
noncomputable def tripleModule : Mℤ ⟶ Mℤ :=
  ConcreteCategory.ofHom (C := TopModuleCat ℤ) (X := Mℤ) (Y := Mℤ)
    ((3 : ℤ) • ContinuousLinearMap.id ℤ Mℤ)

local notation "f₂" => doubleCoefficients
local notation "g₃" => tripleModule

/-- Moving both variables gives a tensor detected as six and hence nonzero. -/
theorem integer_weighted_nonzero :
    TensorProduct.lid ℤ ℤ
      (((Functor.uncurry.obj (TopModuleCat.tensorBifunctor ℤ)).map (f₂ ×ₘ g₃)).hom τ) = 6 ∧
      ((Functor.uncurry.obj (TopModuleCat.tensorBifunctor ℤ)).map (f₂ ×ₘ g₃)).hom τ ≠ 0 := by
  have h₂ : ModuleCat.Hom.hom doubleCoefficients (1 : Cℤ) = (2 : Cℤ) := by
    calc
      _ = ((2 : ℤ) • (LinearMap.id : Cℤ →ₗ[ℤ] Cℤ)) (1 : Cℤ) := by
        simp only [ModuleCat.Hom.hom, doubleCoefficients, ConcreteCategory.hom_ofHom]
      _ = (ModuleCat.isModule TensorMapExamples.integerCoefficients).smul (2 : ℤ) (1 : Cℤ) :=
        LinearMap.smul_apply (2 : ℤ) LinearMap.id (1 : Cℤ)
      _ = 2 := by
        simpa only [Int.zsmul_eq_mul, mul_one] using
          int_smul_eq_zsmul (ModuleCat.isModule TensorMapExamples.integerCoefficients)
            (2 : ℤ) (1 : Cℤ)
  have h₃ : TopModuleCat.Hom.hom tripleModule (1 : Mℤ) = (3 : Mℤ) := by
    calc
      _ = ((3 : ℤ) • ContinuousLinearMap.id ℤ Mℤ) (1 : Mℤ) := by
        simp only [TopModuleCat.Hom.hom, tripleModule, ConcreteCategory.hom_ofHom]
      _ = (ModuleCat.isModule (TopModuleCat.toModuleCat TensorMapExamples.integerModule)).smul
          (3 : ℤ) (1 : Mℤ) :=
        smul_apply (ContinuousLinearMap.id ℤ Mℤ) (3 : ℤ) (1 : Mℤ)
      _ = 3 := by
        simpa only [Int.zsmul_eq_mul, mul_one] using
          int_smul_eq_zsmul
            (ModuleCat.isModule (TopModuleCat.toModuleCat TensorMapExamples.integerModule))
            (3 : ℤ) (1 : Mℤ)
  let T : TensorMapExamples.integerTensor →L[ℤ] TensorMapExamples.integerTensor :=
    TopModuleCat.Hom.hom
      ((Functor.uncurry.obj (TopModuleCat.tensorBifunctor ℤ)).map
        (doubleCoefficients ×ₘ tripleModule))
  have hmap : T = TopModuleCat.tensorMapBilinear ℤ Cℤ Cℤ Mℤ Mℤ
      (ModuleCat.Hom.hom doubleCoefficients) (TopModuleCat.Hom.hom tripleModule) :=
    TopModuleCat.tensorBifunctor_uncurry_map_hom ℤ doubleCoefficients tripleModule
  have hvalue : T τ = (2 : Cℤ) ⊗ₜ[ℤ] (3 : Mℤ) := by
    exact Eq.trans (DFunLike.congr_fun hmap τ)
      (Eq.trans
        (TopModuleCat.tensorMapBilinear_tmul ℤ
          (ModuleCat.Hom.hom doubleCoefficients) (TopModuleCat.Hom.hom tripleModule)
          (1 : Cℤ) (1 : Mℤ))
        (congrArg₂ (fun (c : Cℤ) (m : Mℤ) ↦ c ⊗ₜ[ℤ] m) h₂ h₃))
  have hdet : TensorProduct.lid ℤ ℤ (T τ) = 6 := by
    calc
      _ = TensorProduct.lid ℤ ℤ ((2 : Cℤ) ⊗ₜ[ℤ] (3 : Mℤ)) :=
        congrArg (TensorProduct.lid ℤ ℤ) hvalue
      _ = (2 : ℤ) * 3 := by
        simpa only [smul_eq_mul] using
          (TensorProduct.lid_tmul (R := ℤ) (M := ℤ) (3 : ℤ) (2 : ℤ))
      _ = 6 := by norm_num
  change TensorProduct.lid ℤ ℤ (T τ) = 6 ∧ T τ ≠ 0
  constructor
  · exact hdet
  · intro h
    have hzero : TensorProduct.lid ℤ ℤ (0 : TensorMapExamples.integerTensor) = 0 :=
      (TensorProduct.lid ℤ ℤ).map_zero
    rw [h] at hdet
    replace hdet := hzero.symm.trans hdet
    norm_num at hdet

end TensorBifunctorExamples
