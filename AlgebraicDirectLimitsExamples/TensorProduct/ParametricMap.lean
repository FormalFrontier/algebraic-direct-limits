/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicDirectLimits.Topology.TensorProduct.Map
public import Mathlib.LinearAlgebra.Basis.Fin
public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import Mathlib.Topology.Algebra.Ring.Real

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# A rank-dropping family of tensor maps

The parameter is real, the algebraic left module is the usual real plane, and the
right module is the usual real line. The left family is `diag(b, 0)` and the right
family is `(b + 1) • id`. The joint tensor-map continuity theorem applies on the
entire one-sided tensor, with its original topology.

Mathlib's right unitor detects the first-axis tensor at parameter two as `(6, 0)`.
The nonzero second-axis tensor lies in the kernel for every parameter, and the
whole tensor map vanishes at parameters zero and minus one. Thus the use requires
neither invertibility nor a positive, constant rank. Two additional boundary
lemmas cover a zero left module and an empty parameter space.

## References

This example uses Mathlib's `Module.Basis.finTwoProd`, tensor right unitor and
standard real topological-module structures. The tensor-map and finite-coordinate
APIs are reused from AlgebraicDirectLimits. Mathlib's basis API is due to Johannes
Hölzl, Mario Carneiro and the authors credited in the imported basis modules; its
tensor unitors are due to Kenny Lau and Mario Carneiro. This module is an original
Formal Frontier contribution developed with AI assistance.
-/

@[expose] public section

open scoped TensorProduct

namespace ParametricTensorMapExamples

/-- The real plane with its given algebraic module structure. -/
abbrev planeCoefficients : ModuleCat ℝ := ModuleCat.of ℝ (ℝ × ℝ)

/-- The real line with its usual topology and scalar action. -/
noncomputable abbrev realLine : TopModuleCat ℝ := TopModuleCat.of ℝ ℝ

/-- The canonical one-sided tensor of the real plane and real line. -/
noncomputable abbrev planeTensor : TopModuleCat ℝ :=
  TopModuleCat.tensorLeftObj ℝ planeCoefficients realLine

/-- The stock two-element basis of the real plane. -/
noncomputable abbrev planeBasis : Module.Basis (Fin 2) ℝ planeCoefficients :=
  Module.Basis.finTwoProd ℝ

/-- The left family retains the first coordinate, scaled by the parameter. -/
noncomputable def leftFamily (b : ℝ) : planeCoefficients →ₗ[ℝ] planeCoefficients :=
  b • ((LinearMap.inl ℝ ℝ ℝ).comp (LinearMap.fst ℝ ℝ ℝ))

/-- The left family is the diagonal map with entries `b` and zero. -/
@[simp]
theorem leftFamily_apply (b : ℝ) (v : planeCoefficients) :
    leftFamily b v = (b * v.1, 0) := by
  simp [leftFamily, smul_eq_mul]

/-- The right family scales the original real line by the parameter plus one. -/
noncomputable def rightFamily (b : ℝ) : realLine →L[ℝ] realLine :=
  (b + 1) • ContinuousLinearMap.id ℝ realLine

/-- Evaluation of the right family is ordinary multiplication. -/
@[simp]
theorem rightFamily_apply (b : ℝ) (t : realLine) :
    rightFamily b t = (b + 1) * t := by
  simp [rightFamily, smul_eq_mul]

/-- Every left matrix coefficient is continuous in the real parameter. -/
theorem continuous_leftFamily_coeff (i j : Fin 2) :
    Continuous (fun b : ℝ ↦ planeBasis.repr (leftFamily b (planeBasis i)) j) := by
  have hrepr (b : ℝ) :
      planeBasis.repr (leftFamily b (planeBasis i)) j =
        ![b * (planeBasis i).1, (0 : ℝ)] j := by
    calc
      planeBasis.repr (leftFamily b (planeBasis i)) j =
          ![(leftFamily b (planeBasis i)).1, (leftFamily b (planeBasis i)).2] j :=
        congrFun (Module.Basis.coe_finTwoProd_repr (leftFamily b (planeBasis i))) j
      _ = _ := congrArg (fun v : ℝ × ℝ ↦ ![v.1, v.2] j)
        (leftFamily_apply b (planeBasis i))
  have hcoords : Continuous (fun b : ℝ ↦ ![b * (planeBasis i).1, (0 : ℝ)] j) := by
    fin_cases j
    · exact (continuous_id.mul continuous_const :
        Continuous (fun b : ℝ ↦ b * (planeBasis i).1))
    · exact (continuous_const : Continuous (fun _ : ℝ ↦ (0 : ℝ)))
  exact hcoords.congr (fun b ↦ (hrepr b).symm)

/-- Right evaluation is jointly continuous, without an operator-family premise. -/
theorem continuous_rightFamily_apply :
    Continuous (fun p : ℝ × realLine ↦ rightFamily p.1 p.2) := by
  exact ((continuous_fst.add continuous_const).mul continuous_snd :
    Continuous (fun p : ℝ × realLine ↦ (p.1 + 1) * p.2)).congr
      (fun p ↦ (rightFamily_apply p.1 p.2).symm)

/-- The varying tensor map is jointly continuous on all tensors in the original
one-sided topology, by the generic coefficientwise-left and joint-right theorem. -/
theorem continuous_plane_tensorMap :
    Continuous (fun p : ℝ × planeTensor ↦
      TopModuleCat.tensorMapCLM ℝ (leftFamily p.1) (rightFamily p.1) p.2) := by
  exact TopModuleCat.continuous_tensorMapCLM_apply ℝ planeBasis planeBasis
    leftFamily rightFamily continuous_leftFamily_coeff continuous_rightFamily_apply

/-- The first-axis tensor with right scalar one. -/
noncomputable def firstTensor : planeTensor :=
  ((1, 0) : planeCoefficients) ⊗ₜ[ℝ] (1 : realLine)

/-- The second-axis tensor with right scalar one. -/
noncomputable def kernelTensor : planeTensor :=
  ((0, 1) : planeCoefficients) ⊗ₜ[ℝ] (1 : realLine)

/-- The right unitor detects the two input tensors as the two standard plane vectors. -/
theorem axisTensors_rid :
    TensorProduct.rid ℝ (ℝ × ℝ) firstTensor = (1, 0) ∧
      TensorProduct.rid ℝ (ℝ × ℝ) kernelTensor = (0, 1) := by
  constructor <;> simp [firstTensor, kernelTensor]

/-- Both exhibited tensors are nonzero in the retained algebraic carrier. -/
theorem axisTensors_ne_zero : firstTensor ≠ 0 ∧ kernelTensor ≠ 0 := by
  constructor
  · intro h
    have hraw : (firstTensor : (ℝ × ℝ) ⊗[ℝ] ℝ) = 0 := h
    have he : TensorProduct.rid ℝ (ℝ × ℝ)
        (0 : (ℝ × ℝ) ⊗[ℝ] ℝ) = (1, 0) :=
      (congrArg (fun z : (ℝ × ℝ) ⊗[ℝ] ℝ ↦
        TensorProduct.rid ℝ (ℝ × ℝ) z) hraw).symm.trans axisTensors_rid.1
    have hf := congrArg Prod.fst he
    norm_num at hf
  · intro h
    have hraw : (kernelTensor : (ℝ × ℝ) ⊗[ℝ] ℝ) = 0 := h
    have he : TensorProduct.rid ℝ (ℝ × ℝ)
        (0 : (ℝ × ℝ) ⊗[ℝ] ℝ) = (0, 1) :=
      (congrArg (fun z : (ℝ × ℝ) ⊗[ℝ] ℝ ↦
        TensorProduct.rid ℝ (ℝ × ℝ) z) hraw).symm.trans axisTensors_rid.2
    have hs := congrArg Prod.snd he
    norm_num at hs

/-- The pure-tensor map identity specialized to the real plane and line. -/
private theorem tensorMap_tmul_raw (b : ℝ) (v : ℝ × ℝ) (t : ℝ) :
    (TopModuleCat.tensorMapCLM ℝ (leftFamily b) (rightFamily b) (v ⊗ₜ[ℝ] t) :
      (ℝ × ℝ) ⊗[ℝ] ℝ) =
        ((b * v.1, 0) : ℝ × ℝ) ⊗ₜ[ℝ] ((b + 1) * t) := by
  have hmap :
      (TopModuleCat.tensorMapCLM ℝ (leftFamily b) (rightFamily b) (v ⊗ₜ[ℝ] t) :
        (ℝ × ℝ) ⊗[ℝ] ℝ) =
        (leftFamily b v : ℝ × ℝ) ⊗ₜ[ℝ] (rightFamily b t : ℝ) :=
    TopModuleCat.tensorMapCLM_tmul ℝ (leftFamily b) (rightFamily b) v t
  have hvalues :
      ((leftFamily b v : ℝ × ℝ) ⊗ₜ[ℝ] (rightFamily b t : ℝ) :
        (ℝ × ℝ) ⊗[ℝ] ℝ) =
        ((b * v.1, 0) : ℝ × ℝ) ⊗ₜ[ℝ] ((b + 1) * t) :=
    congrArg₂ (fun (w : ℝ × ℝ) (s : ℝ) ↦ w ⊗ₜ[ℝ] s)
      (leftFamily_apply b v) (rightFamily_apply b t)
  exact Eq.trans hmap hvalues

/-- The right unitor detects the first-axis output as the scalar polynomial `b(b+1)`. -/
theorem tensorMap_firstTensor_rid (b : ℝ) :
    TensorProduct.rid ℝ (ℝ × ℝ)
        (TopModuleCat.tensorMapCLM ℝ (leftFamily b) (rightFamily b) firstTensor) =
      (b * (b + 1), 0) := by
  have hmap :
      (TopModuleCat.tensorMapCLM ℝ (leftFamily b) (rightFamily b) firstTensor :
        (ℝ × ℝ) ⊗[ℝ] ℝ) = ((b, 0) : ℝ × ℝ) ⊗ₜ[ℝ] (b + 1) := by
    simpa only [firstTensor, mul_one] using tensorMap_tmul_raw b (1, 0) 1
  calc
    TensorProduct.rid ℝ (ℝ × ℝ)
        (TopModuleCat.tensorMapCLM ℝ (leftFamily b) (rightFamily b) firstTensor) =
        TensorProduct.rid ℝ (ℝ × ℝ) (((b, 0) : ℝ × ℝ) ⊗ₜ[ℝ] (b + 1)) :=
      congrArg (fun z : (ℝ × ℝ) ⊗[ℝ] ℝ ↦ TensorProduct.rid ℝ (ℝ × ℝ) z) hmap
    _ = (b * (b + 1), 0) := by
      rw [TensorProduct.rid_tmul]
      change ((b + 1) * b, (b + 1) * (0 : ℝ)) = (b * (b + 1), 0)
      exact Prod.ext (mul_comm _ _) (mul_zero _)

/-- At parameter two the output is detected as `(6, 0)` and hence is nonzero. -/
theorem tensorMap_at_two_nonzero :
    TensorProduct.rid ℝ (ℝ × ℝ)
        (TopModuleCat.tensorMapCLM ℝ (leftFamily 2) (rightFamily 2) firstTensor) = (6, 0) ∧
      TopModuleCat.tensorMapCLM ℝ (leftFamily 2) (rightFamily 2) firstTensor ≠ 0 := by
  have hdet : TensorProduct.rid ℝ (ℝ × ℝ)
      (TopModuleCat.tensorMapCLM ℝ (leftFamily 2) (rightFamily 2) firstTensor) = (6, 0) := by
    rw [tensorMap_firstTensor_rid]
    norm_num
  refine ⟨hdet, ?_⟩
  intro h
  have hraw :
      (TopModuleCat.tensorMapCLM ℝ (leftFamily 2) (rightFamily 2) firstTensor :
        (ℝ × ℝ) ⊗[ℝ] ℝ) = 0 := h
  have he : TensorProduct.rid ℝ (ℝ × ℝ)
      (0 : (ℝ × ℝ) ⊗[ℝ] ℝ) = (6, 0) :=
    (congrArg (fun z : (ℝ × ℝ) ⊗[ℝ] ℝ ↦
      TensorProduct.rid ℝ (ℝ × ℝ) z) hraw).symm.trans hdet
  have hf := congrArg Prod.fst he
  norm_num at hf

/-- A fixed nonzero tensor is killed for every parameter, so no member is injective. -/
theorem tensorMap_kills_kernelTensor (b : ℝ) :
    kernelTensor ≠ 0 ∧
      TopModuleCat.tensorMapCLM ℝ (leftFamily b) (rightFamily b) kernelTensor = 0 := by
  refine ⟨axisTensors_ne_zero.2, ?_⟩
  change (TopModuleCat.tensorMapCLM ℝ (leftFamily b) (rightFamily b) kernelTensor :
    (ℝ × ℝ) ⊗[ℝ] ℝ) = (0 : (ℝ × ℝ) ⊗[ℝ] ℝ)
  have hmap :
      (TopModuleCat.tensorMapCLM ℝ (leftFamily b) (rightFamily b) kernelTensor :
        (ℝ × ℝ) ⊗[ℝ] ℝ) =
        ((b * 0, 0) : ℝ × ℝ) ⊗ₜ[ℝ] ((b + 1) * 1) :=
    tensorMap_tmul_raw b (0, 1) 1
  have hzero :
      (((b * 0, 0) : ℝ × ℝ) ⊗ₜ[ℝ] ((b + 1) * 1) :
        (ℝ × ℝ) ⊗[ℝ] ℝ) = (0 : (ℝ × ℝ) ⊗[ℝ] ℝ) := by
    simp only [mul_zero, mul_one]
    change (0 : ℝ × ℝ) ⊗ₜ[ℝ] (b + 1) = (0 : (ℝ × ℝ) ⊗[ℝ] ℝ)
    exact TensorProduct.zero_tmul (R := ℝ) (ℝ × ℝ) (b + 1)
  exact Eq.trans hmap hzero

/-- The whole endomorphism vanishes at zero and minus one, unlike its value at two. -/
theorem tensorMap_rank_drop :
    TopModuleCat.tensorMapCLM ℝ (leftFamily 0) (rightFamily 0) =
        (0 : planeTensor →L[ℝ] planeTensor) ∧
      TopModuleCat.tensorMapCLM ℝ (leftFamily (-1)) (rightFamily (-1)) =
        (0 : planeTensor →L[ℝ] planeTensor) := by
  have hleft : leftFamily 0 = (0 : planeCoefficients →ₗ[ℝ] planeCoefficients) := by
    simp [leftFamily]
  have hright : rightFamily (-1) = (0 : realLine →L[ℝ] realLine) := by
    apply ContinuousLinearMap.ext
    intro t
    rw [rightFamily_apply, zero_apply]
    norm_num
  constructor
  · exact (congrArg (fun f : planeCoefficients →ₗ[ℝ] planeCoefficients ↦
      TopModuleCat.tensorMapCLM ℝ f (rightFamily 0)) hleft).trans
        (TopModuleCat.tensorMapCLM_zero_left ℝ (rightFamily 0))
  · exact (congrArg (fun g : realLine →L[ℝ] realLine ↦
      TopModuleCat.tensorMapCLM ℝ (leftFamily (-1)) g) hright).trans
        (TopModuleCat.tensorMapCLM_zero_right ℝ (leftFamily (-1)))

section Boundaries

universe uR uX uC uD uM uN

variable (R : Type uR) [CommRing R] [TopologicalSpace R]
variable {X : Type uX} [TopologicalSpace X]
variable {C : ModuleCat.{uC} R} {D : ModuleCat.{uD} R}
variable {M : TopModuleCat.{uM} R} {N : TopModuleCat.{uN} R}

/-- A zero left module gives a constant-zero family on the whole tensor input;
no family regularity is needed in this boundary case. -/
theorem continuous_tensorMap_subsingleton_left [Subsingleton C]
    (f : X → C →ₗ[R] D) (g : X → M →L[R] N) :
    Continuous (fun p : X × TopModuleCat.tensorLeftObj R C M ↦
      TopModuleCat.tensorMapCLM R (f p.1) (g p.1) p.2) := by
  have hf (x : X) : f x = 0 := by
    ext c
    have hc : c = 0 := Subsingleton.elim _ _
    simp [hc]
  simpa only [hf, TopModuleCat.tensorMapCLM_zero_left, zero_apply] using
    (continuous_const : Continuous (fun _ : X × TopModuleCat.tensorLeftObj R C M ↦
      (0 : TopModuleCat.tensorLeftObj R D N)))

/-- With an empty parameter space the joint evaluation domain is empty. -/
theorem continuous_tensorMap_isEmpty [IsEmpty X]
    (f : X → C →ₗ[R] D) (g : X → M →L[R] N) :
    Continuous (fun p : X × TopModuleCat.tensorLeftObj R C M ↦
      TopModuleCat.tensorMapCLM R (f p.1) (g p.1) p.2) := by
  exact continuous_iff_continuousAt.mpr (fun p ↦ isEmptyElim p.1)

end Boundaries

end ParametricTensorMapExamples
