/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicDirectLimits.Topology.TensorProduct
public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.LinearAlgebra.Basis.Fin
public import Mathlib.Topology.Instances.Int
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

/-!
# Integer-pair tensor generators and boundary cases

The diagonal algebra map `ℤ → ℤ × ℤ` is proper and its coefficient module has
the existing basis `Module.Basis.finTwoProd ℤ`. Tensoring with `M = ℤ` gives a
nonzero generator with coordinates `(1, 0)`; doubling on the right factor moves
it. The doubling is constructed with the canonical continuous tensor-map API;
its effect agrees with the algebraic map and is detected by algebraic coordinates.
No continuity of the coordinate map is needed for this calculation.

An empty coefficient basis and a trivial scalar ring give zero tensor carriers.
They are boundary cases, distinct from the nonzero integer-pair example.
-/

@[expose] public section

open scoped TensorProduct

universe uR uC uM

namespace TensorProductExamples

/-- The rank-two integer coefficient module. -/
abbrev integerPairCoefficients : ModuleCat ℤ := ModuleCat.of ℤ (ℤ × ℤ)

/-- The integers with their usual discrete topology, as a topological integer module. -/
abbrev integerModule : TopModuleCat ℤ := TopModuleCat.of ℤ ℤ

/-- The diagonal integer algebra map is not surjective. -/
theorem integerDiagonal_not_surjective :
    ¬ Function.Surjective (algebraMap ℤ (ℤ × ℤ)) := by
  intro h
  obtain ⟨n, hn⟩ := h (1, 0)
  have h₁ := congrArg Prod.fst hn
  have h₀ := congrArg Prod.snd hn
  change n = 1 at h₁
  change n = 0 at h₀
  exact one_ne_zero (h₁.symm.trans h₀)

/-- The tensor generator at `(1, 0)`, applied to `1`. -/
noncomputable def firstGeneratorTensor :
    TopModuleCat.tensorLeftObj ℤ integerPairCoefficients integerModule :=
  TopModuleCat.tensorGenerator ℤ integerPairCoefficients integerModule (1, 0) 1

/-- The first generator has one nonzero coordinate. -/
theorem firstGeneratorTensor_coordinates :
    TopModuleCat.tensorCoordinateLinearEquiv ℤ integerPairCoefficients integerModule
      (Module.Basis.finTwoProd ℤ) firstGeneratorTensor = ![1, 0] := by
  ext i
  calc
    TopModuleCat.tensorCoordinateLinearEquiv ℤ integerPairCoefficients integerModule
        (Module.Basis.finTwoProd ℤ) firstGeneratorTensor i =
        (Module.Basis.finTwoProd ℤ).repr (1, 0) i • (1 : ℤ) :=
      TopModuleCat.tensorCoordinateLinearEquiv_tensorGenerator_apply ℤ
        integerPairCoefficients integerModule (Module.Basis.finTwoProd ℤ) (1, 0) 1 i
    _ = ![1, 0] i := by
      rw [congrFun (Module.Basis.coe_finTwoProd_repr ((1, 0) : ℤ × ℤ)) i]
      fin_cases i <;> norm_num

/-- The inverse coordinate map reconstructs the first generator. -/
theorem integerPair_coordinates_inverse :
    (TopModuleCat.tensorCoordinateLinearEquiv ℤ integerPairCoefficients integerModule
      (Module.Basis.finTwoProd ℤ)).symm ![1, 0] = firstGeneratorTensor := by
  apply (TopModuleCat.tensorCoordinateLinearEquiv ℤ integerPairCoefficients integerModule
    (Module.Basis.finTwoProd ℤ)).injective
  exact ((TopModuleCat.tensorCoordinateLinearEquiv ℤ integerPairCoefficients integerModule
    (Module.Basis.finTwoProd ℤ)).apply_symm_apply ![1, 0]).trans
      firstGeneratorTensor_coordinates.symm

/-- Tensoring a nonzero integer with the first coefficient vector is nonzero. -/
theorem firstGeneratorTensor_ne_zero : firstGeneratorTensor ≠ 0 := by
  intro h
  have h₀ := congrFun firstGeneratorTensor_coordinates (0 : Fin 2)
  rw [h] at h₀
  have hz := congrFun (map_zero
    (TopModuleCat.tensorCoordinateLinearEquiv ℤ integerPairCoefficients integerModule
      (Module.Basis.finTwoProd ℤ))) (0 : Fin 2)
  exact zero_ne_one (hz.symm.trans h₀)

/-- Apply the algebraic tensor map induced by doubling on the right factor. -/
noncomputable def doubledFirstTensor :
    TopModuleCat.tensorLeftObj ℤ integerPairCoefficients integerModule :=
  TensorProduct.map (LinearMap.id : integerPairCoefficients →ₗ[ℤ] integerPairCoefficients)
    (2 • LinearMap.id : integerModule →ₗ[ℤ] integerModule) firstGeneratorTensor

/-- The doubled tensor has first coordinate `2`. -/
theorem doubledFirstTensor_coordinate_zero :
    TopModuleCat.tensorCoordinateLinearEquiv ℤ integerPairCoefficients integerModule
      (Module.Basis.finTwoProd ℤ) doubledFirstTensor 0 = 2 := by
  have hrepr : (Module.Basis.finTwoProd ℤ).repr (1, 0) (0 : Fin 2) = 1 :=
    congrFun (Module.Basis.coe_finTwoProd_repr ((1, 0) : ℤ × ℤ)) (0 : Fin 2)
  norm_num [doubledFirstTensor, firstGeneratorTensor, hrepr]

/-- The right-factor tensor map is not the identity on this generator. -/
theorem doubledFirstTensor_ne_first : doubledFirstTensor ≠ firstGeneratorTensor := by
  intro h
  have h₀ := congrFun firstGeneratorTensor_coordinates (0 : Fin 2)
  have h₂ := doubledFirstTensor_coordinate_zero
  rw [h] at h₂
  have heq : (2 : ℤ) = 1 := h₂.symm.trans h₀
  norm_num at heq

/-- Doubling as a continuous linear endomorphism of the integer module. -/
noncomputable def integerDoubling : integerModule →L[ℤ] integerModule :=
  2 • ContinuousLinearMap.id ℤ integerModule

/-- The underlying linear map of integer doubling is twice the identity. -/
@[simp]
theorem integerDoubling_toLinearMap :
    integerDoubling.toLinearMap = (2 • LinearMap.id : integerModule →ₗ[ℤ] integerModule) := rfl

/-- Integer doubling sends `1` to `2`. -/
@[simp]
theorem integerDoubling_apply_one : integerDoubling (1 : integerModule) = 2 := by
  norm_num [integerDoubling]

/-- The canonical continuous tensor map induced by left identity and right doubling. -/
noncomputable def integerTensorDoubling :
    TopModuleCat.tensorLeftObj ℤ integerPairCoefficients integerModule →L[ℤ]
      TopModuleCat.tensorLeftObj ℤ integerPairCoefficients integerModule :=
  TopModuleCat.tensorMapCLM ℤ
    (LinearMap.id : integerPairCoefficients →ₗ[ℤ] integerPairCoefficients) integerDoubling

/-- The canonical continuous map sends the first generator to its value at `2`. -/
theorem integerTensorDoubling_firstGenerator_apply :
    integerTensorDoubling firstGeneratorTensor =
      TopModuleCat.tensorGenerator ℤ integerPairCoefficients integerModule (1, 0) 2 := by
  exact (TopModuleCat.tensorMapCLM_tensorGenerator_apply ℤ
    (LinearMap.id : integerPairCoefficients →ₗ[ℤ] integerPairCoefficients)
    integerDoubling ((1, 0) : integerPairCoefficients) (1 : integerModule)).trans
      (congrArg (TopModuleCat.tensorGenerator ℤ integerPairCoefficients integerModule
        ((1, 0) : integerPairCoefficients)) integerDoubling_apply_one)

/-- On the first generator, the canonical continuous map agrees with the algebraic doubling. -/
theorem integerTensorDoubling_firstGenerator :
    integerTensorDoubling firstGeneratorTensor = doubledFirstTensor := by
  exact (TopModuleCat.tensorMapCLM_apply ℤ
    (LinearMap.id : integerPairCoefficients →ₗ[ℤ] integerPairCoefficients)
    integerDoubling firstGeneratorTensor).trans
      (congrArg (fun q : integerModule →ₗ[ℤ] integerModule ↦
        TensorProduct.map
          (LinearMap.id : integerPairCoefficients →ₗ[ℤ] integerPairCoefficients)
          q firstGeneratorTensor) integerDoubling_toLinearMap)

/-- The canonical continuous tensor map moves the nonzero first generator. -/
theorem integerTensorDoubling_firstGenerator_ne :
    integerTensorDoubling firstGeneratorTensor ≠ firstGeneratorTensor := by
  rw [integerTensorDoubling_firstGenerator]
  exact doubledFirstTensor_ne_first

/-- The constructed continuous tensor endomorphism is not the identity. -/
theorem integerTensorDoubling_ne_id :
    integerTensorDoubling ≠ ContinuousLinearMap.id ℤ
      (TopModuleCat.tensorLeftObj ℤ integerPairCoefficients integerModule) := by
  intro h
  apply integerTensorDoubling_firstGenerator_ne
  simpa only [ContinuousLinearMap.id_apply] using DFunLike.congr_fun h firstGeneratorTensor

/-- Algebraic change to the swapped two-vector basis interchanges coordinate positions. -/
theorem integerPair_basisChange_first :
    ((TopModuleCat.tensorCoordinateLinearEquiv ℤ integerPairCoefficients integerModule
      (Module.Basis.finTwoProd ℤ)).symm.trans
      (TopModuleCat.tensorCoordinateLinearEquiv ℤ integerPairCoefficients integerModule
        ((Module.Basis.finTwoProd ℤ).reindex (Equiv.swap (0 : Fin 2) 1)))) ![1, 0] =
      ![0, 1] := by
  rw [LinearEquiv.trans_apply, integerPair_coordinates_inverse]
  ext k
  have hrepr (i : Fin 2) : (Module.Basis.finTwoProd ℤ).repr (1, 0) i = ![1, 0] i :=
    congrFun (Module.Basis.coe_finTwoProd_repr ((1, 0) : ℤ × ℤ)) i
  fin_cases k <;>
    norm_num [firstGeneratorTensor, Module.Basis.repr_reindex_apply, hrepr]

section Boundaries

variable (R : Type uR) [CommRing R] [TopologicalSpace R]

/-- An empty coefficient basis gives the zero tensor, with no restriction on the right factor. -/
theorem emptyCoefficient_tensor_eq_zero (M : TopModuleCat.{uM} R)
    (x : TopModuleCat.tensorLeftObj R (ModuleCat.of R (Fin 0 → R)) M) : x = 0 := by
  apply (TopModuleCat.tensorCoordinateLinearEquiv R (ModuleCat.of R (Fin 0 → R)) M
    (Module.Basis.empty (Fin 0 → R) : Module.Basis (Fin 0) R (Fin 0 → R))).injective
  ext i
  exact Fin.elim0 i

/-- The empty coordinate product reconstructs zero. -/
theorem emptyCoefficient_coordinates_symm (M : TopModuleCat.{uM} R) (x : Fin 0 → M) :
    (TopModuleCat.tensorCoordinateLinearEquiv R (ModuleCat.of R (Fin 0 → R)) M
      (Module.Basis.empty (Fin 0 → R) : Module.Basis (Fin 0) R (Fin 0 → R))).symm x = 0 := by
  rw [TopModuleCat.tensorCoordinateLinearEquiv_symm_apply]
  simp

/-- Over a trivial ring, every tensor is zero, independently of finite-freeness. -/
theorem trivialRing_tensor_eq_zero [Subsingleton R] (C : ModuleCat.{uC} R)
    (M : TopModuleCat.{uM} R) (x : TopModuleCat.tensorLeftObj R C M) : x = 0 := by
  have := Module.subsingleton R (TopModuleCat.tensorLeftObj R C M)
  exact Subsingleton.elim _ _

/-- Canonical finite-free coordinates use the existing finite chosen-basis index,
including for trivial scalar rings. -/
theorem chosenBasis_tensorGenerator_apply (C : ModuleCat.{uC} R) (M : TopModuleCat.{uM} R)
    [Module.Free R C] [Module.Finite R C] (c : C) (m : M)
    (i : Module.Free.ChooseBasisIndex R C) :
    TopModuleCat.tensorCoordinateLinearEquiv R C M (Module.Free.chooseBasis R C)
      (TopModuleCat.tensorGenerator R C M c m) i =
        (Module.Free.chooseBasis R C).repr c i • m := by
  exact TopModuleCat.tensorCoordinateLinearEquiv_tensorGenerator_apply R C M
    (Module.Free.chooseBasis R C) c m i

end Boundaries

/-- Continuous finite-basis tensor coordinates for the rank-two integer coefficient module. -/
noncomputable def integerPairContinuousCoordinates :
    TopModuleCat.tensorLeftObj ℤ integerPairCoefficients integerModule ≃L[ℤ]
      (Fin 2 → integerModule) :=
  TopModuleCat.tensorCoordinateContinuousLinearEquiv ℤ
    integerPairCoefficients integerModule (Module.Basis.finTwoProd ℤ)

/-- The continuous coordinates of the first generator are `![1, 0]`. -/
theorem integerPairContinuousCoordinates_first :
    integerPairContinuousCoordinates firstGeneratorTensor = ![1, 0] := by
  exact (TopModuleCat.tensorCoordinateContinuousLinearEquiv_apply ℤ
    integerPairCoefficients integerModule (Module.Basis.finTwoProd ℤ) firstGeneratorTensor).trans
      firstGeneratorTensor_coordinates

/-- The inverse continuous coordinates reconstruct the first generator. -/
theorem integerPairContinuousCoordinates_inverse_first :
    integerPairContinuousCoordinates.symm ![1, 0] = firstGeneratorTensor := by
  apply integerPairContinuousCoordinates.injective
  exact (integerPairContinuousCoordinates.apply_symm_apply ![1, 0]).trans
    integerPairContinuousCoordinates_first.symm

/-- The first coordinate as a continuous linear map, using the canonical Pi projection. -/
noncomputable def integerFirstContinuousCoordinate :
    TopModuleCat.tensorLeftObj ℤ integerPairCoefficients integerModule →L[ℤ]
      integerModule :=
  (ContinuousLinearMap.proj (R := ℤ)
    (φ := fun _ : Fin 2 ↦ integerModule) (0 : Fin 2)).comp
      integerPairContinuousCoordinates.toContinuousLinearMap

/-- The first continuous coordinate of the first generator is `1`. -/
theorem integerFirstContinuousCoordinate_first :
    integerFirstContinuousCoordinate firstGeneratorTensor = 1 := by
  calc
    integerFirstContinuousCoordinate firstGeneratorTensor =
        integerPairContinuousCoordinates firstGeneratorTensor 0 := rfl
    _ = 1 := congrFun integerPairContinuousCoordinates_first (0 : Fin 2)

/-- Right-factor doubling is detected by the first continuous coordinate, with value `2`. -/
theorem integerFirstContinuousCoordinate_doubling_first :
    integerFirstContinuousCoordinate
      (integerTensorDoubling firstGeneratorTensor) = 2 := by
  calc
    integerFirstContinuousCoordinate (integerTensorDoubling firstGeneratorTensor) =
        integerPairContinuousCoordinates (integerTensorDoubling firstGeneratorTensor) 0 := rfl
    _ = TopModuleCat.tensorCoordinateLinearEquiv ℤ integerPairCoefficients integerModule
        (Module.Basis.finTwoProd ℤ) doubledFirstTensor 0 := by
      rw [integerTensorDoubling_firstGenerator]
      exact congrFun (TopModuleCat.tensorCoordinateContinuousLinearEquiv_apply ℤ
        integerPairCoefficients integerModule (Module.Basis.finTwoProd ℤ) doubledFirstTensor)
          (0 : Fin 2)
    _ = 2 := doubledFirstTensor_coordinate_zero

/-- The first projection retracts the proper inclusion of integer coefficients. -/
theorem integerPair_fst_comp_inl :
    (LinearMap.fst ℤ ℤ ℤ : integerPairCoefficients →ₗ[ℤ] ModuleCat.of ℤ ℤ).comp
        (LinearMap.inl ℤ ℤ ℤ) =
      (LinearMap.id : ModuleCat.of ℤ ℤ →ₗ[ℤ] ModuleCat.of ℤ ℤ) :=
  LinearMap.fst_comp_inl ℤ ℤ ℤ

/-- The inclusion into the first integer coordinate misses `(0, 1)`. -/
theorem integerPair_inl_not_surjective :
    ¬ Function.Surjective
      (LinearMap.inl ℤ ℤ ℤ : ModuleCat.of ℤ ℤ →ₗ[ℤ] integerPairCoefficients) := by
  intro h
  obtain ⟨n, hn⟩ := h (0, 1)
  have h₁ := congrArg Prod.snd hn
  change (0 : ℤ) = 1 at h₁
  exact zero_ne_one h₁

/-- Tensoring the first-coordinate inclusion with the integer identity remains split. -/
theorem integerTensorPair_leftInverse :
    Function.LeftInverse
      (TopModuleCat.tensorMapCLM ℤ (C := integerPairCoefficients) (D := ModuleCat.of ℤ ℤ)
        (M := integerModule) (N := integerModule)
        (LinearMap.fst ℤ ℤ ℤ) (ContinuousLinearMap.id ℤ integerModule))
      (TopModuleCat.tensorMapCLM ℤ (C := ModuleCat.of ℤ ℤ) (D := integerPairCoefficients)
        (M := integerModule) (N := integerModule)
        (LinearMap.inl ℤ ℤ ℤ) (ContinuousLinearMap.id ℤ integerModule)) := by
  apply ContinuousLinearMap.leftInverse_of_comp
  exact TopModuleCat.tensorMapCLM_comp_eq_id ℤ
    (C := ModuleCat.of ℤ ℤ) (D := integerPairCoefficients)
    (M := integerModule) (N := integerModule)
    (LinearMap.inl ℤ ℤ ℤ) (LinearMap.fst ℤ ℤ ℤ)
    (ContinuousLinearMap.id ℤ integerModule) (ContinuousLinearMap.id ℤ integerModule)
    integerPair_fst_comp_inl
    (ContinuousLinearMap.id_comp (ContinuousLinearMap.id ℤ integerModule))

/-- The tensor inclusion sends `1 ⊗ 1` to the existing first generator. -/
theorem integerTensorPair_inl_tmul_one :
    TopModuleCat.tensorMapCLM ℤ (C := ModuleCat.of ℤ ℤ) (D := integerPairCoefficients)
        (M := integerModule) (N := integerModule)
        (LinearMap.inl ℤ ℤ ℤ) (ContinuousLinearMap.id ℤ integerModule)
        ((1 : ℤ) ⊗ₜ[ℤ] (1 : integerModule)) = firstGeneratorTensor := by
  have hmap :
      TopModuleCat.tensorMapCLM ℤ (C := ModuleCat.of ℤ ℤ) (D := integerPairCoefficients)
        (M := integerModule) (N := integerModule)
        (LinearMap.inl ℤ ℤ ℤ) (ContinuousLinearMap.id ℤ integerModule)
        ((1 : ℤ) ⊗ₜ[ℤ] (1 : integerModule)) =
      (show TopModuleCat.tensorLeftObj ℤ integerPairCoefficients integerModule from
        ((1, 0) : integerPairCoefficients) ⊗ₜ[ℤ] (1 : integerModule)) := by
    simpa only [LinearMap.inl_apply, ContinuousLinearMap.id_apply] using
      (TopModuleCat.tensorMapCLM_tmul ℤ (C := ModuleCat.of ℤ ℤ)
        (D := integerPairCoefficients) (M := integerModule) (N := integerModule)
        (LinearMap.inl ℤ ℤ ℤ) (ContinuousLinearMap.id ℤ integerModule)
        (1 : ℤ) (1 : integerModule))
  have hgen :
      (show TopModuleCat.tensorLeftObj ℤ integerPairCoefficients integerModule from
        ((1, 0) : integerPairCoefficients) ⊗ₜ[ℤ] (1 : integerModule)) =
      firstGeneratorTensor :=
    (TopModuleCat.tensorGenerator_apply ℤ integerPairCoefficients integerModule (1, 0) 1).symm
  exact Eq.trans (α := TopModuleCat.tensorLeftObj ℤ integerPairCoefficients integerModule)
    hmap hgen

/-- The source tensor `1 ⊗ 1` is nonzero, detected by the independently nonzero image. -/
theorem integerTensor_tmul_one_ne_zero :
    (show TopModuleCat.tensorLeftObj ℤ (ModuleCat.of ℤ ℤ) integerModule from
      (1 : ℤ) ⊗ₜ[ℤ] (1 : integerModule)) ≠ 0 := by
  intro h
  let I : TopModuleCat.tensorLeftObj ℤ (ModuleCat.of ℤ ℤ) integerModule →L[ℤ]
      TopModuleCat.tensorLeftObj ℤ integerPairCoefficients integerModule :=
    TopModuleCat.tensorMapCLM ℤ (C := ModuleCat.of ℤ ℤ) (D := integerPairCoefficients)
      (M := integerModule) (N := integerModule)
      (LinearMap.inl ℤ ℤ ℤ) (ContinuousLinearMap.id ℤ integerModule)
  have himage :
      I (show TopModuleCat.tensorLeftObj ℤ (ModuleCat.of ℤ ℤ) integerModule from
        (1 : ℤ) ⊗ₜ[ℤ] (1 : integerModule)) = firstGeneratorTensor :=
    integerTensorPair_inl_tmul_one
  have hzero :
      I (show TopModuleCat.tensorLeftObj ℤ (ModuleCat.of ℤ ℤ) integerModule from
        (1 : ℤ) ⊗ₜ[ℤ] (1 : integerModule)) = 0 :=
    (congrArg (fun z : TopModuleCat.tensorLeftObj ℤ (ModuleCat.of ℤ ℤ) integerModule ↦
      I z) h).trans I.map_zero
  exact firstGeneratorTensor_ne_zero (himage.symm.trans hzero)

/-- The split tensor inclusion has a nonzero value on `1 ⊗ 1`. -/
theorem integerTensorPair_inl_tmul_one_ne_zero :
    TopModuleCat.tensorMapCLM ℤ (C := ModuleCat.of ℤ ℤ) (D := integerPairCoefficients)
        (M := integerModule) (N := integerModule)
        (LinearMap.inl ℤ ℤ ℤ) (ContinuousLinearMap.id ℤ integerModule)
        ((1 : ℤ) ⊗ₜ[ℤ] (1 : integerModule)) ≠ 0 := by
  rw [integerTensorPair_inl_tmul_one]
  exact firstGeneratorTensor_ne_zero

/-- The tensor inclusion is proper: the second coordinate vanishes on its whole image
but is `1` on `(0, 1) ⊗ 1`. -/
theorem integerTensorPair_inl_not_surjective :
    ¬ Function.Surjective
      (TopModuleCat.tensorMapCLM ℤ (C := ModuleCat.of ℤ ℤ) (D := integerPairCoefficients)
        (M := integerModule) (N := integerModule)
        (LinearMap.inl ℤ ℤ ℤ) (ContinuousLinearMap.id ℤ integerModule)) := by
  let I : TopModuleCat.tensorLeftObj ℤ (ModuleCat.of ℤ ℤ) integerModule →L[ℤ]
      TopModuleCat.tensorLeftObj ℤ integerPairCoefficients integerModule :=
    TopModuleCat.tensorMapCLM ℤ (C := ModuleCat.of ℤ ℤ) (D := integerPairCoefficients)
      (M := integerModule) (N := integerModule)
      (LinearMap.inl ℤ ℤ ℤ) (ContinuousLinearMap.id ℤ integerModule)
  change ¬ Function.Surjective I
  let q : TopModuleCat.tensorLeftObj ℤ integerPairCoefficients integerModule →L[ℤ]
      integerModule :=
    (ContinuousLinearMap.proj (R := ℤ)
      (φ := fun _ : Fin 2 ↦ integerModule) (1 : Fin 2)).comp
        integerPairContinuousCoordinates.toContinuousLinearMap
  have hqI (z : TopModuleCat.tensorLeftObj ℤ (ModuleCat.of ℤ ℤ) integerModule) :
      q (I z) = 0 := by
    induction z using TensorProduct.inductionOn with
    | tmul n m =>
      change integerPairContinuousCoordinates (I (n ⊗ₜ[ℤ] m)) 1 = 0
      dsimp only [I]
      rw [TopModuleCat.tensorMapCLM_tmul, LinearMap.inl_apply,
        ContinuousLinearMap.id_apply]
      change TopModuleCat.tensorCoordinateContinuousLinearEquiv ℤ
        integerPairCoefficients integerModule (Module.Basis.finTwoProd ℤ)
        (((n, 0) : integerPairCoefficients) ⊗ₜ[ℤ] m) (1 : Fin 2) = 0
      simpa only [congrFun (Module.Basis.coe_finTwoProd_repr ((n, 0) : ℤ × ℤ))
        (1 : Fin 2), Matrix.cons_val_one, Matrix.cons_val_zero, zero_smul] using
        (TopModuleCat.tensorCoordinateContinuousLinearEquiv_tmul_apply ℤ
          integerPairCoefficients integerModule (Module.Basis.finTwoProd ℤ)
          ((n, 0) : integerPairCoefficients) m (1 : Fin 2))
    | add x y hx hy =>
      have hadd : q (I (x + y)) = q (I x) + q (I y) :=
        (q.comp I).map_add
          (show TopModuleCat.tensorLeftObj ℤ (ModuleCat.of ℤ ℤ) integerModule from x)
          (show TopModuleCat.tensorLeftObj ℤ (ModuleCat.of ℤ ℤ) integerModule from y)
      exact hadd.trans
        ((congrArg₂ (fun a b : integerModule ↦ a + b) hx hy).trans
          (add_zero (0 : integerModule)))
  have hqw : q (((0, 1) : integerPairCoefficients) ⊗ₜ[ℤ] (1 : integerModule)) = 1 := by
    change TopModuleCat.tensorCoordinateContinuousLinearEquiv ℤ
      integerPairCoefficients integerModule (Module.Basis.finTwoProd ℤ)
      (((0, 1) : integerPairCoefficients) ⊗ₜ[ℤ] (1 : integerModule)) (1 : Fin 2) = 1
    simpa only [congrFun (Module.Basis.coe_finTwoProd_repr ((0, 1) : ℤ × ℤ))
      (1 : Fin 2), Matrix.cons_val_one, Matrix.cons_val_zero, one_smul] using
      (TopModuleCat.tensorCoordinateContinuousLinearEquiv_tmul_apply ℤ
        integerPairCoefficients integerModule (Module.Basis.finTwoProd ℤ)
        ((0, 1) : integerPairCoefficients) (1 : integerModule) (1 : Fin 2))
  intro h
  obtain ⟨z, hz⟩ := h (((0, 1) : integerPairCoefficients) ⊗ₜ[ℤ] (1 : integerModule))
  exact zero_ne_one ((hqI z).symm.trans ((congrArg q hz).trans hqw))

section ContinuousBoundaries

universe uι

variable (R : Type uR) [CommRing R] [TopologicalSpace R]

/-- Continuous coordinates for an empty coefficient basis and any right factor. -/
noncomputable def emptyCoefficientContinuousCoordinates (M : TopModuleCat.{uM} R) :
    TopModuleCat.tensorLeftObj R (ModuleCat.of R (Fin 0 → R)) M ≃L[R]
      (Fin 0 → M) :=
  TopModuleCat.tensorCoordinateContinuousLinearEquiv R
    (ModuleCat.of R (Fin 0 → R)) M
    (Module.Basis.empty (Fin 0 → R) : Module.Basis (Fin 0) R (Fin 0 → R))

/-- The inverse continuous coordinates of the empty product reconstruct zero. -/
theorem emptyCoefficientContinuousCoordinates_symm (M : TopModuleCat.{uM} R)
    (x : Fin 0 → M) :
    (emptyCoefficientContinuousCoordinates R M).symm x = 0 := by
  calc
    (emptyCoefficientContinuousCoordinates R M).symm x =
        ∑ i : Fin 0, TopModuleCat.tensorGenerator R (ModuleCat.of R (Fin 0 → R)) M
          ((Module.Basis.empty (Fin 0 → R) : Module.Basis (Fin 0) R (Fin 0 → R)) i)
          (x i) :=
      TopModuleCat.tensorCoordinateContinuousLinearEquiv_symm_apply R
        (ModuleCat.of R (Fin 0 → R)) M (Module.Basis.empty (Fin 0 → R)) x
    _ = 0 := emptyCoefficient_tensor_eq_zero R M _

/-- Over a trivial scalar ring, the inverse continuous coordinates reconstruct zero. -/
theorem trivialRing_continuousCoordinate_symm_eq_zero [Subsingleton R]
    (C : ModuleCat.{uC} R) (M : TopModuleCat.{uM} R) {ι : Type uι} [Finite ι]
    (b : Module.Basis ι R C) (x : ι → M) :
    (TopModuleCat.tensorCoordinateContinuousLinearEquiv R C M b).symm x = 0 := by
  exact trivialRing_tensor_eq_zero R C M _

/-- Canonical finite-free continuous coordinates reconstruct the sum of chosen-basis generators,
including for trivial scalar rings. -/
theorem chosenBasis_continuousCoordinates_symm_apply (C : ModuleCat.{uC} R)
    (M : TopModuleCat.{uM} R) [Module.Free R C] [Module.Finite R C]
    (x : Module.Free.ChooseBasisIndex R C → M) :
    (TopModuleCat.tensorCoordinateContinuousLinearEquiv R C M
      (Module.Free.chooseBasis R C)).symm x =
        ∑ i : Module.Free.ChooseBasisIndex R C,
          TopModuleCat.tensorGenerator R C M ((Module.Free.chooseBasis R C) i) (x i) := by
  exact TopModuleCat.tensorCoordinateContinuousLinearEquiv_symm_apply R C M
    (Module.Free.chooseBasis R C) x

end ContinuousBoundaries

end TensorProductExamples
