/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicDirectLimits.Topology.RestrictionKernels
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.Topology.Instances.Int
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring

/-!
# A nonzero kernel under restriction from `ZMod 4` to the integers

Equip `ZMod 4` with the discrete topology and restrict its regular module along
integer reduction modulo four. Doubling is nonzero, its kernel is `{0, 2}`, and
its square and its sum with itself are zero. The chosen categorical kernel has
a nonzero element over `2`, constructed using `kernel.lift`. Mathlib's kernel
comparison and preservation isomorphism take that element to an element over
`2` in the kernel of restricted doubling.

The scalar map is not injective. The restricted module has a nonzero element
annihilated by the nonzero integer `4`, and is not free over the integers. All
scalar formulas use the stored module dictionary of the restriction object.

## References

The residue arithmetic uses Mathlib's `Data.ZMod.Basic`. The categorical
kernel lift, comparison and preservation isomorphism use Kim Morrison's
`CategoryTheory.Limits.Shapes.Kernels` and
`CategoryTheory.Limits.Preserves.Shapes.Kernels`. The nonfreeness argument
uses the torsion-free instance for free modules in Riccardo Brasca's
`LinearAlgebra.FreeModule.Basic` and Yaël Dillies' torsion-free module API.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace ScalarRestriction.ModFour

/-- Discrete topology on the residue ring modulo four. -/
@[instance_reducible]
def topology : TopologicalSpace (ZMod 4) := ⊥

/-- The discrete topology on `ZMod 4` used for restriction of scalars to `ℤ`. -/
local instance instTopologicalSpaceZModFour : TopologicalSpace (ZMod 4) := topology
local instance : DiscreteTopology (ZMod 4) := discreteTopology_bot _

/-- The unital reduction homomorphism from the integers to `ZMod 4`. -/
def reduction : ℤ →+* ZMod 4 := Int.castRingHom (ZMod 4)

/-- Reduction modulo four has its usual integer-cast values. -/
@[simp]
theorem reduction_apply (n : ℤ) : reduction n = (n : ZMod 4) := rfl

/-- Reduction is continuous for the discrete integer topology. -/
theorem continuous_reduction : Continuous reduction := continuous_of_discreteTopology

/-- Reduction modulo four is not injective. -/
theorem reduction_not_injective : ¬ Function.Injective reduction := by
  intro h
  have hfour : (4 : ℤ) = 0 := h (by change (4 : ZMod 4) = 0; decide)
  exact (by decide : (4 : ℤ) ≠ 0) hfour

/-- The regular topological module over the discrete ring `ZMod 4`. -/
noncomputable abbrev regularModule : TopModuleCat (ZMod 4) :=
  TopModuleCat.of (ZMod 4) (ZMod 4)

/-- The canonical same-topology integer module obtained by restriction. -/
noncomputable abbrev restrictedModule : TopModuleCat ℤ :=
  TopModuleCat.restrictScalarsObj reduction continuous_reduction regularModule

/-- The action in the restricted module is multiplication by the residue of
its integer scalar, using the stored restricted module structure. -/
theorem restricted_smul (n : ℤ) (x : regularModule) :
    @SMul.smul ℤ restrictedModule restrictedModule.isModule.toSMul n x =
      reduction n * x :=
  TopModuleCat.restrictScalarsObj_smul reduction continuous_reduction regularModule n x

/-- Every element of the restricted module is annihilated by the integer `4`. -/
theorem restricted_four_smul (x : regularModule) :
    @SMul.smul ℤ restrictedModule restrictedModule.isModule.toSMul 4 x = 0 := by
  rw [restricted_smul]
  have hfour : reduction 4 = 0 := by change (4 : ZMod 4) = 0; decide
  rw [hfour, zero_mul]

/-- The canonical restricted module is not free over the integers: its nonzero
unit is annihilated by the nonzero scalar `4`. -/
theorem restrictedModule_not_free :
    ¬ @Module.Free ℤ restrictedModule inferInstance
      restrictedModule.isAddCommGroup.toAddCommMonoid restrictedModule.isModule := by
  intro h
  let : Module ℤ restrictedModule := restrictedModule.isModule
  let : Module.Free ℤ restrictedModule := h
  have ht : (4 : ℤ) • (show restrictedModule from (1 : ZMod 4)) = 0 :=
    restricted_four_smul 1
  have hone : (show restrictedModule from (1 : ZMod 4)) = 0 :=
    (smul_eq_zero_iff_right (by decide : (4 : ℤ) ≠ 0)).mp ht
  exact (by decide : (1 : ZMod 4) ≠ 0) hone

/-- Doubling on the regular `ZMod 4` module, as a continuous linear morphism. -/
noncomputable def doubling : regularModule ⟶ regularModule :=
  TopModuleCat.ofHom
    (ContinuousLinearMap.id (ZMod 4) regularModule +
      ContinuousLinearMap.id (ZMod 4) regularModule)

/-- Doubling adds each residue to itself. -/
@[simp]
theorem doubling_apply (x : regularModule) : doubling x = x + x := rfl

/-- The continuous linear morphism is multiplication by `2`. -/
theorem doubling_eq_two_mul (x : regularModule) : doubling x = (2 : ZMod 4) * x := by
  rw [doubling_apply, two_mul]

/-- Doubling is not the zero morphism. -/
theorem doubling_ne_zero : doubling ≠ 0 := by
  intro h
  have hx := congrArg (fun g : regularModule ⟶ regularModule ↦ g 1) h
  change (1 : ZMod 4) + 1 = 0 at hx
  exact (by decide : (1 : ZMod 4) + 1 ≠ 0) hx

/-- The concrete kernel of doubling consists exactly of `0` and `2`. -/
theorem doubling_kernel_iff (x : regularModule) : doubling x = 0 ↔ x = 0 ∨ x = 2 := by
  rw [doubling_apply]
  let z : ZMod 4 := x
  have hx : x = (ZMod.val (n := 4) z : ZMod 4) :=
    (ZMod.natCast_zmod_val (n := 4) z).symm
  have hlt : ZMod.val (n := 4) z < 4 := ZMod.val_lt (n := 4) z
  interval_cases ZMod.val (n := 4) z <;> rw [hx] <;> decide

private theorem twice_doubling (x : ZMod 4) : (x + x) + (x + x) = 0 := by
  calc
    (x + x) + (x + x) = (4 : ZMod 4) * x := by ring
    _ = 0 := by rw [show (4 : ZMod 4) = 0 by decide, zero_mul]

/-- The square of doubling is zero, allowing a nonzero lift into its kernel. -/
theorem doubling_comp_self : doubling ≫ doubling = 0 := by
  refine ConcreteCategory.ext_apply (C := TopModuleCat.{0} (ZMod 4))
    (fun (x : regularModule) ↦ ?_)
  change (x + x) + (x + x) = 0
  exact twice_doubling x

/-- The sum of doubling with itself is zero. -/
theorem doubling_add_self : doubling + doubling = 0 := by
  refine ConcreteCategory.ext_apply (C := TopModuleCat.{0} (ZMod 4))
    (fun (x : regularModule) ↦ ?_)
  change (x + x) + (x + x) = 0
  exact twice_doubling x

/-- Additivity and zero preservation apply to this nonzero morphism after
canonical restriction, not just to the zero hom-set element. -/
theorem restricted_doubling_add_self :
    (TopModuleCat.restrictScalars reduction continuous_reduction).map doubling +
      (TopModuleCat.restrictScalars reduction continuous_reduction).map doubling = 0 := by
  rw [← Functor.map_add, doubling_add_self, Functor.map_zero]

/-- The canonical restricted morphism still multiplies residues by `2`. -/
theorem restricted_doubling_apply (x : restrictedModule) :
    (TopModuleCat.restrictScalars reduction continuous_reduction).map doubling x =
      (2 : ZMod 4) * x := by
  rw [TopModuleCat.restrictScalars_map_apply, doubling_eq_two_mul]

/-- An element of the chosen categorical kernel lying over the nonzero residue `2`.
It is obtained from the stock universal lift of doubling, since its square is zero. -/
noncomputable def kernelTwo : kernel (C := TopModuleCat.{0} (ZMod 4)) doubling :=
  kernel.lift (C := TopModuleCat.{0} (ZMod 4)) doubling doubling doubling_comp_self
    (1 : regularModule)

/-- The kernel inclusion sends the chosen element to `2`. -/
@[simp]
theorem kernelTwo_ι : kernel.ι doubling kernelTwo = (2 : ZMod 4) := by
  have h := congrArg (fun g : regularModule ⟶ regularModule ↦ g 1)
    (kernel.lift_ι doubling doubling doubling_comp_self)
  calc
    kernel.ι doubling kernelTwo = doubling (1 : regularModule) := by
      simpa only [kernelTwo, ConcreteCategory.comp_apply] using h
    _ = (2 : ZMod 4) := by rw [doubling_apply]; decide

/-- The chosen categorical kernel is nonzero. -/
theorem kernelTwo_ne_zero : kernelTwo ≠ 0 := by
  intro h
  have hz : (kernel.ι doubling).hom
      (0 : kernel (C := TopModuleCat.{0} (ZMod 4)) doubling) = 0 := map_zero _
  have htwo : (2 : ZMod 4) = 0 :=
    kernelTwo_ι.symm.trans ((congrArg (kernel.ι doubling).hom h).trans hz)
  exact (by decide : (2 : ZMod 4) ≠ 0) htwo

/-- The stock kernel comparison sends the element over `2` to an element over `2`
in the kernel of the canonically restricted morphism. -/
theorem kernelComparison_kernelTwo_ι :
    kernel.ι ((TopModuleCat.restrictScalars reduction continuous_reduction).map doubling)
      (kernelComparison doubling (TopModuleCat.restrictScalars reduction continuous_reduction)
        (show (TopModuleCat.restrictScalars reduction continuous_reduction).obj
          (kernel doubling) from kernelTwo)) = (2 : ZMod 4) := by
  have h := congrArg
    (fun g :
      (TopModuleCat.restrictScalars reduction continuous_reduction).obj (kernel doubling) ⟶
        (TopModuleCat.restrictScalars reduction continuous_reduction).obj regularModule ↦
      g (show (TopModuleCat.restrictScalars reduction continuous_reduction).obj
        (kernel doubling) from kernelTwo))
    (kernelComparison_comp_ι (f := doubling)
      (TopModuleCat.restrictScalars reduction continuous_reduction))
  have p1 : @Eq (ZMod 4)
      (kernel.ι ((TopModuleCat.restrictScalars reduction continuous_reduction).map doubling)
        (kernelComparison doubling (TopModuleCat.restrictScalars reduction continuous_reduction)
          (show (TopModuleCat.restrictScalars reduction continuous_reduction).obj
            (kernel doubling) from kernelTwo)))
      ((show (TopModuleCat.restrictScalars reduction continuous_reduction).obj (kernel doubling) ⟶
          (TopModuleCat.restrictScalars reduction continuous_reduction).obj regularModule from
          kernelComparison doubling (TopModuleCat.restrictScalars reduction continuous_reduction) ≫
            kernel.ι ((TopModuleCat.restrictScalars reduction continuous_reduction).map doubling))
        (show (TopModuleCat.restrictScalars reduction continuous_reduction).obj
          (kernel doubling) from kernelTwo)) :=
    (ConcreteCategory.comp_apply (C := TopModuleCat.{0} ℤ)
      (X := (TopModuleCat.restrictScalars reduction continuous_reduction).obj (kernel doubling))
      (Y := kernel (C := TopModuleCat.{0} ℤ)
        ((TopModuleCat.restrictScalars reduction continuous_reduction).map doubling))
      (Z := (TopModuleCat.restrictScalars reduction continuous_reduction).obj regularModule)
      (kernelComparison doubling (TopModuleCat.restrictScalars reduction continuous_reduction))
      (kernel.ι ((TopModuleCat.restrictScalars reduction continuous_reduction).map doubling))
      (show (TopModuleCat.restrictScalars reduction continuous_reduction).obj
        (kernel doubling) from kernelTwo)).symm
  have p2 : @Eq (ZMod 4)
      ((show (TopModuleCat.restrictScalars reduction continuous_reduction).obj (kernel doubling) ⟶
          (TopModuleCat.restrictScalars reduction continuous_reduction).obj regularModule from
          kernelComparison doubling (TopModuleCat.restrictScalars reduction continuous_reduction) ≫
            kernel.ι ((TopModuleCat.restrictScalars reduction continuous_reduction).map doubling))
        (show (TopModuleCat.restrictScalars reduction continuous_reduction).obj
          (kernel doubling) from kernelTwo))
      ((show (TopModuleCat.restrictScalars reduction continuous_reduction).obj (kernel doubling) ⟶
          (TopModuleCat.restrictScalars reduction continuous_reduction).obj regularModule from
          (TopModuleCat.restrictScalars reduction continuous_reduction).map (kernel.ι doubling))
        (show (TopModuleCat.restrictScalars reduction continuous_reduction).obj
          (kernel doubling) from kernelTwo)) := h
  have p3 : @Eq (ZMod 4)
      ((show (TopModuleCat.restrictScalars reduction continuous_reduction).obj (kernel doubling) ⟶
          (TopModuleCat.restrictScalars reduction continuous_reduction).obj regularModule from
          (TopModuleCat.restrictScalars reduction continuous_reduction).map (kernel.ι doubling))
        (show (TopModuleCat.restrictScalars reduction continuous_reduction).obj
          (kernel doubling) from kernelTwo))
      (kernel.ι doubling kernelTwo) :=
    TopModuleCat.restrictScalars_map_apply reduction continuous_reduction
      (M := kernel (C := TopModuleCat.{0} (ZMod 4)) doubling) (N := regularModule)
      (kernel.ι doubling)
      (show (TopModuleCat.restrictScalars reduction continuous_reduction).obj
        (kernel doubling) from kernelTwo)
  exact Eq.trans (α := ZMod 4) p1
    (Eq.trans (α := ZMod 4) p2 (Eq.trans (α := ZMod 4) p3 kernelTwo_ι))

/-- The preservation isomorphism carries a nonzero element to the kernel of the
restricted morphism. Its forward map is the stock kernel comparison. -/
theorem preservesKernel_iso_kernelTwo_ne_zero :
    (PreservesKernel.iso (TopModuleCat.restrictScalars reduction continuous_reduction)
      doubling).hom
      (show (TopModuleCat.restrictScalars reduction continuous_reduction).obj
        (kernel doubling) from kernelTwo) ≠ 0 := by
  rw [PreservesKernel.iso_hom]
  intro h
  have hvalue := kernelComparison_kernelTwo_ι
  rw [h] at hvalue
  have hz :
      (kernel.ι ((TopModuleCat.restrictScalars reduction continuous_reduction).map doubling)).hom
        (0 : kernel (C := TopModuleCat.{0} ℤ)
          ((TopModuleCat.restrictScalars reduction continuous_reduction).map doubling)) =
            0 := map_zero _
  have htwo : (0 : ZMod 4) = 2 := hz.symm.trans hvalue
  exact (by decide : (0 : ZMod 4) ≠ 2) htwo

end ScalarRestriction.ModFour
