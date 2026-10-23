/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicDirectLimits.Topology.DualTensorHom
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Rectangular operators and continuous dual tensors

A real two-to-three operator is constructed independently from coordinate
functionals, then reconstructed by the continuous contraction of its column
tensor. The inverse of the finite-left continuous equivalence recovers the same
column tensor from the independent operator. Its value at `![-2, 1]` is the
nonzero vector `![0, -7, 1]`. The zero-dimensional left source gives only the zero
operator and zero inverse tensor, for any topological right module with continuous
addition and scalar action.

## References

These examples follow Formal Frontier Agents' rectangular dual-tensor model.
They use `TopModuleCat.dualTensorHom` and `dualTensorHomEquiv` through their
characteristic and inverse APIs, and Mathlib's continuous coordinate projections,
product assembly and finite-vector notation. The contraction module credits the algebraic and
bounded-convergence constructions.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

namespace AlgebraicDirectLimitsExamples.DualTensorHom

/-- The coordinate functionals on the real plane. -/
def realCoordinate (i : Fin 2) : StrongDual ℝ (Fin 2 → ℝ) :=
  ContinuousLinearMap.proj i

/-- The tensor of the columns of a nonidentity rectangular operator. -/
def rectangularTensor : StrongDual ℝ (Fin 2 → ℝ) ⊗[ℝ] (Fin 3 → ℝ) :=
  realCoordinate 0 ⊗ₜ[ℝ] ![1, 3, 0] + realCoordinate 1 ⊗ₜ[ℝ] ![2, -1, 1]

/-- The continuous real operator `(x₀,x₁) ↦ (x₀+2x₁,3x₀−x₁,x₁)`,
constructed independently of the tensor map. -/
def rectangularOperator : (Fin 2 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  ContinuousLinearMap.pi ![realCoordinate 0 + (2 : ℝ) • realCoordinate 1,
    (3 : ℝ) • realCoordinate 0 - realCoordinate 1, realCoordinate 1]

/-- Applying the tensor lift recovers the independently constructed operator. -/
theorem rectangular_reconstruction :
    TopModuleCat.dualTensorHom ℝ (Fin 2 → ℝ) (Fin 3 → ℝ) rectangularTensor =
      rectangularOperator := by
  calc
    _ = TopModuleCat.dualTensorHom ℝ (Fin 2 → ℝ) (Fin 3 → ℝ)
          (realCoordinate 0 ⊗ₜ[ℝ] ![1, 3, 0]) +
        TopModuleCat.dualTensorHom ℝ (Fin 2 → ℝ) (Fin 3 → ℝ)
          (realCoordinate 1 ⊗ₜ[ℝ] ![2, -1, 1]) :=
      (TopModuleCat.dualTensorHom ℝ (Fin 2 → ℝ) (Fin 3 → ℝ)).map_add _ _
    _ = _ := by
      ext x i
      rw [add_apply, TopModuleCat.dualTensorHom_tmul,
        TopModuleCat.dualTensorHom_tmul]
      fin_cases i <;>
        simp [rectangularOperator, realCoordinate, sub_eq_add_neg] <;> ring

/-- The continuous inverse recovers the column tensor from the independently
constructed two-to-three operator. -/
theorem rectangular_inverse :
    (TopModuleCat.dualTensorHomEquiv ℝ (Fin 2 → ℝ) (Fin 3 → ℝ)).symm
      rectangularOperator = rectangularTensor := by
  exact (congrArg (TopModuleCat.dualTensorHomEquiv ℝ (Fin 2 → ℝ) (Fin 3 → ℝ)).symm
    rectangular_reconstruction).symm.trans
      (TopModuleCat.dualTensorHomEquiv_symm_dualTensorHom ℝ (Fin 2 → ℝ) (Fin 3 → ℝ)
        rectangularTensor)

/-- A nonzero input gives a nonzero output with both positive and negative coordinates. -/
theorem rectangular_value : rectangularOperator ![-2, 1] = ![0, -7, 1] := by
  ext i
  fin_cases i <;> norm_num [rectangularOperator, realCoordinate]

/-- With a zero-dimensional left source, every tensor gives the zero operator,
for an arbitrary topological right module. -/
theorem zero_left (G : Type*) [AddCommGroup G] [Module ℝ G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [ContinuousSMul ℝ G]
    (z : TopModuleCat.tensorLeftObj ℝ (ModuleCat.of ℝ (StrongDual ℝ (Fin 0 → ℝ)))
      (TopModuleCat.of ℝ G)) :
    TopModuleCat.dualTensorHom ℝ (Fin 0 → ℝ) G z = 0 := by
  ext x
  simp only [show x = 0 from Subsingleton.elim _ _, map_zero]

/-- Every operator out of the zero-dimensional left source has zero inverse
tensor, without a norm or finiteness assumption on the right module. -/
theorem zero_left_inverse (G : Type*) [AddCommGroup G] [Module ℝ G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [ContinuousSMul ℝ G] (A : (Fin 0 → ℝ) →L[ℝ] G) :
    (TopModuleCat.dualTensorHomEquiv ℝ (Fin 0 → ℝ) G).symm A = 0 := by
  have hA : A = 0 := by
    rw [← TopModuleCat.dualTensorHom_dualTensorHomEquiv_symm ℝ (Fin 0 → ℝ) G A]
    exact zero_left G _
  rw [hA, map_zero]

end AlgebraicDirectLimitsExamples.DualTensorHom
