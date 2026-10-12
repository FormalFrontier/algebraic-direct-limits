/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicDirectLimits.Topology.TensorCompactness
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.Topology.Algebra.Group.ZPow
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Instances.Int
public import Mathlib.Topology.Instances.ZMod

/-!
# A finite torsion example for tensor compactness

The coefficient and right factor use the canonical integer action on `ZMod 3`,
with the discrete topology on the right factor. The coefficient is finitely
generated but not free over the integers. Multiplication detects the nonzero
pure tensor `1 ⊗ 1` without any compactness assertion about the tensor.

The compactness statement for finitely generated coefficients specializes to
the one-sided tensor of these two modules.

## References

The example uses the one-sided tensor and generator API of Algebraic Direct
Limits. It reuses Mathlib's integer-module API by Nathaniel Thomas, Jeremy
Avigad, Johannes Hölzl and Mario Carneiro; its `ZMod` development by Eric
Rodriguez and Chris Hughes; the discrete `ZMod` topology by David Loeffler; and
the integer topology by Johannes Hölzl and Mario Carneiro. The bilinear
multiplication and tensor APIs are due to Kenny Lau, Yury Kudryashov and Mario
Carneiro. Finite generation reuses Johan Commelin's development; nonfreeness
uses Riccardo Brasca's free-module and Yaël Dillies's torsion-free APIs.
Finite-space compactness reuses the topology development by Johannes Hölzl,
Mario Carneiro and Yury Kudryashov.
-/

@[expose] public section

open scoped TensorProduct

namespace TensorProductExamples

/-- The integers modulo three, with their canonical integer-module structure. -/
abbrev C3 : ModuleCat ℤ := ModuleCat.of ℤ (ZMod 3)

/-- The integers modulo three, with their discrete topology and canonical integer action. -/
abbrev M3 : TopModuleCat ℤ := TopModuleCat.of ℤ (ZMod 3)

/-- The coefficient carrier is `ZMod 3`. -/
@[simp]
theorem coe_C3 : (C3 : Type) = ZMod 3 := rfl

/-- The right-factor carrier is `ZMod 3`. -/
@[simp]
theorem coe_M3 : (M3 : Type) = ZMod 3 := rfl

/-- The right factor retains Mathlib's discrete topology on `ZMod 3`. -/
theorem M3_topologicalSpace :
    M3.topologicalSpace = (inferInstance : TopologicalSpace (ZMod 3)) := rfl

/-- The coefficient action is multiplication by the integer cast. -/
theorem C3_smul (n : ℤ) (x : C3) : n • x = (n : ZMod 3) * x := by
  change n • (x : ZMod 3) = (n : ZMod 3) * x
  rw [zsmul_eq_mul]

/-- The stored right-factor action is multiplication by the same integer cast. -/
theorem M3_smul (n : ℤ) (x : M3) : n • x = (n : ZMod 3) * x := by
  change n • (x : ZMod 3) = (n : ZMod 3) * x
  rw [zsmul_eq_mul]

/-- The right factor has jointly continuous scalar action for its stored module structure. -/
theorem M3_continuous_smul : Continuous (fun p : ℤ × M3 ↦ p.1 • p.2) :=
  continuous_smul

/-- The coefficient module is finitely generated, independently of tensor compactness. -/
instance C3_moduleFinite : Module.Finite ℤ C3 := Module.Finite.of_finite

/-- The right factor is compact because its carrier is finite. -/
instance M3_compactSpace : CompactSpace M3 := Finite.compactSpace

/-- Every coefficient is an integer multiple of `1`. -/
theorem C3_exists_smul_one (x : C3) : ∃ n : ℤ, n • (1 : C3) = x := by
  obtain ⟨n, hn⟩ := ZMod.intCast_surjective (n := 3) (x : ZMod 3)
  refine ⟨n, (C3_smul n (1 : C3)).trans ?_⟩
  exact (mul_one (n : ZMod 3)).trans hn

/-- The coefficient `1` is nonzero. -/
theorem C3_one_ne_zero : (1 : C3) ≠ 0 := by
  intro hzero
  exact (by decide : (3 : ℕ) ≠ 1)
    ((ZMod.one_eq_zero_iff (n := 3)).mp hzero)

/-- The nonzero integer `3` annihilates the coefficient `1`. -/
theorem C3_three_smul_one : (3 : ℤ) • (1 : C3) = 0 := by
  rw [C3_smul]
  have hcast : ((3 : ℤ) : ZMod 3) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd 3 3).mpr (dvd_refl _)
  rw [hcast, zero_mul]

/-- The coefficient module is not free over the integers. -/
theorem C3_not_free : ¬ Module.Free ℤ C3 := by
  intro hfree
  letI : Module.Free ℤ C3 := hfree
  have hthree : (3 : ℤ) ≠ 0 := by decide
  have hone : (1 : C3) = 0 :=
    (smul_eq_zero_iff_right (R := ℤ) (M := C3) hthree).mp C3_three_smul_one
  exact C3_one_ne_zero hone

/-- Multiplication lifted from the canonical integer actions of the two factors. -/
noncomputable def tensorMultiplicationModThree : TensorProduct ℤ C3 M3 →ₗ[ℤ] ZMod 3 :=
  LinearMap.mul' ℤ (ZMod 3)

/-- The lifted multiplication sends a pure tensor to the product of its factors. -/
@[simp]
theorem tensorMultiplicationModThree_tmul (c : C3) (m : M3) :
    tensorMultiplicationModThree (c ⊗ₜ[ℤ] m) = c * m := rfl

/-- The pure tensor of the two unit residues in the one-sided topological tensor. -/
noncomputable def tensorUnitModThree : TopModuleCat.tensorLeftObj ℤ C3 M3 :=
  (1 : C3) ⊗ₜ[ℤ] (1 : M3)

/-- The unit tensor is the value at `1` of the continuous generator at `1`. -/
theorem tensorUnitModThree_eq_tensorGenerator :
    tensorUnitModThree = TopModuleCat.tensorGenerator ℤ C3 M3 (1 : C3) (1 : M3) := rfl

/-- Multiplication detects the unit tensor by its nonzero image `1`. -/
@[simp]
theorem tensorMultiplicationModThree_unit :
    tensorMultiplicationModThree tensorUnitModThree = 1 := by
  change tensorMultiplicationModThree ((1 : C3) ⊗ₜ[ℤ] (1 : M3)) = (1 : ZMod 3)
  exact (tensorMultiplicationModThree_tmul (1 : C3) (1 : M3)).trans
    (one_mul (1 : ZMod 3))

/-- The unit tensor is nonzero in the carrier of the one-sided topological tensor. -/
theorem tensorUnitModThree_ne_zero : tensorUnitModThree ≠ 0 := by
  intro hzero
  change tensorUnitModThree = (0 : TensorProduct ℤ C3 M3) at hzero
  have hmul : tensorMultiplicationModThree tensorUnitModThree = (0 : ZMod 3) :=
    (tensorMultiplicationModThree.congr_arg hzero).trans tensorMultiplicationModThree.map_zero
  exact C3_one_ne_zero (tensorMultiplicationModThree_unit.symm.trans hmul)

/-- The one-sided tensor of the two residue modules is compact. -/
theorem compactSpace_tensorModThree : CompactSpace (TopModuleCat.tensorLeftObj ℤ C3 M3) :=
  TopModuleCat.compactSpace_tensorLeftObj ℤ C3 M3

end TensorProductExamples
