/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicDirectLimits.Topology.TensorDiscrete
public import AlgebraicDirectLimits.Topology.Restriction
public import AlgebraicDirectLimitsExamples.TensorProduct
public import Mathlib.Algebra.Ring.Prod
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Tactic.NormNum

/-!
# Discrete right-module tensor examples

The integer example has algebraic coefficients `ℕ →₀ ZMod 2`, which are not
finitely generated over `ℤ`. Every single-coordinate vector gives a nonzero
tensor, different coordinates give different tensors, and two-coordinate sums
are detected by the algebraic right unitor. The coefficients and tensors have
nonzero elements annihilated by `2`.

For the product ring `ℤ × ℝ` with its product topology, restriction along the
first projection gives a discrete right module with action `(n, x) • m = n * m`.
The scalars are not discrete. The algebraic left unitor detects nonzero tensors
and sums in the canonical one-sided tensor with coefficients equal to the ring.

## Scope

The tensor action and topology are those of `TopModuleCat.tensorLeftObj`.
The algebraic unitors distinguish tensor vectors; their continuity is not
asserted here. No topology is supplied as input on the coefficient modules.

## References

The right integer module is the integer example of the one-sided tensor API.
Coefficient vectors, their module structures and finite-generation criterion
use Mathlib's Finsupp and dimension APIs, due to Johannes Hölzl, Mario Carneiro,
Sander Dahmen and Kim Morrison. The algebraic unitors are due to Kenny Lau and
Mario Carneiro. Scalar restriction follows the Continuous Group Cohomology
formalization by Formal Frontier Agents, including Beacon's original
development, and uses Mathlib's change-of-rings API by Jujian Zhang. The product
ring, topology and order APIs are due to Johannes Hölzl, Chris Hughes, Mario
Carneiro and Yury Kudryashov.
-/

@[expose] public section

open scoped TensorProduct

namespace DiscreteTensorExamples

open TensorProductExamples (integerModule)

/-- Finitely supported mod-two coefficients with their canonical integer action. -/
noncomputable abbrev modTwoCoefficients : ModuleCat ℤ := ModuleCat.of ℤ (ℕ →₀ ZMod 2)

/-- The canonical tensor of mod-two coefficients with the integer right module. -/
noncomputable abbrev modTwoTensor : TopModuleCat ℤ :=
  TopModuleCat.tensorLeftObj ℤ modTwoCoefficients integerModule

/-- The vector equal to `1` at coordinate `n` and zero elsewhere. -/
noncomputable def modTwoVector (n : ℕ) : modTwoCoefficients := Finsupp.single n 1

/-- Coordinate formula for every single-coordinate vector. -/
@[simp]
theorem modTwoVector_apply (n i : ℕ) :
    modTwoVector n i = if n = i then 1 else 0 :=
  Finsupp.single_apply

/-- Each single-coordinate vector has exactly its indicated support. -/
@[simp]
theorem modTwoVector_support (n : ℕ) : (modTwoVector n).support = {n} :=
  Finsupp.support_single n one_ne_zero

/-- No single-coordinate vector is zero. -/
theorem modTwoVector_ne_zero (n : ℕ) : modTwoVector n ≠ 0 := by
  simpa only [modTwoVector, Finsupp.single_ne_zero] using (one_ne_zero : (1 : ZMod 2) ≠ 0)

/-- These algebraic integer coefficients are not finitely generated. -/
theorem modTwoCoefficients_not_finite : ¬ Module.Finite ℤ modTwoCoefficients := by
  intro h
  have h' : Module.Finite ℤ (ℕ →₀ ZMod 2) := h
  rcases (Module.finite_finsupp_iff (R := ℤ) (M := ZMod 2) (ι := ℕ)).mp h' with
    hEmpty | hSub | hFinite
  · exact not_isEmpty_of_nonempty ℕ hEmpty
  · exact one_ne_zero (hSub.elim (1 : ZMod 2) 0)
  · exact (inferInstance : Infinite ℕ).not_finite hFinite.2

/-- Multiplication by the integer `2` annihilates every coefficient vector. -/
theorem two_smul_modTwoCoefficients (c : modTwoCoefficients) : (2 : ℤ) • c = 0 := by
  ext i
  change (2 : ℤ) • c i = 0
  simpa only [two_zsmul] using ZModModule.add_self (c i)

/-- The integer right module has the full jointly continuous integer action. -/
theorem continuous_integerModule_smul :
    Continuous (fun p : ℤ × integerModule ↦ p.1 • p.2) :=
  integerModule.continuousSMul.continuous_smul

/-- The canonical tensor has the full jointly continuous scalar action supplied
by its topological-module bundle, independently of discreteness. -/
theorem continuous_modTwoTensor_smul :
    Continuous (fun p : ℤ × modTwoTensor ↦ p.1 • p.2) :=
  modTwoTensor.continuousSMul.continuous_smul

-- Whole input and output dictionaries, not only carrier witnesses.
noncomputable example : AddCommGroup modTwoCoefficients := modTwoCoefficients.isAddCommGroup
noncomputable example : Module ℤ modTwoCoefficients := modTwoCoefficients.isModule
example : AddCommGroup integerModule := integerModule.isAddCommGroup
example : Module ℤ integerModule := integerModule.isModule
example : IsTopologicalAddGroup integerModule := integerModule.isTopologicalAddGroup
example : ContinuousAdd integerModule := inferInstance
example : ContinuousSMul ℤ integerModule := integerModule.continuousSMul
example : DiscreteTopology integerModule := inferInstance
noncomputable example : AddCommGroup modTwoTensor := modTwoTensor.isAddCommGroup
noncomputable example : Module ℤ modTwoTensor := modTwoTensor.isModule
example : IsTopologicalAddGroup modTwoTensor := modTwoTensor.isTopologicalAddGroup
example : ContinuousAdd modTwoTensor := inferInstance
example : ContinuousSMul ℤ modTwoTensor := modTwoTensor.continuousSMul
example (r : ℤ) (c d : modTwoCoefficients) : r • (c + d) = r • c + r • d :=
  smul_add r c d
example (r s : ℤ) (c : modTwoCoefficients) : (r + s) • c = r • c + s • c :=
  add_smul r s c
example (c : modTwoCoefficients) : (1 : ℤ) • c = c := one_smul ℤ c

/-- The tensor generator at a single-coordinate coefficient, evaluated at `1`. -/
noncomputable def modTwoTensorVector (n : ℕ) : modTwoTensor :=
  TopModuleCat.tensorGenerator ℤ modTwoCoefficients integerModule (modTwoVector n) 1

/-- The single-coordinate tensor is the corresponding algebraic pure tensor. -/
@[simp]
theorem modTwoTensorVector_eq_tmul (n : ℕ) :
    modTwoTensorVector n = modTwoVector n ⊗ₜ[ℤ] (1 : integerModule) :=
  TopModuleCat.tensorGenerator_apply ℤ modTwoCoefficients integerModule (modTwoVector n) 1

/-- The algebraic right unitor on the bundled mod-two tensor module. -/
private noncomputable def modTwoTensorRid : modTwoTensor ≃ₗ[ℤ] modTwoCoefficients :=
  (LinearEquiv.cast (R := ℤ) (M := fun X : ModuleCat ℤ ↦ (X : Type))
    (show modTwoTensor.toModuleCat =
      ModuleCat.of ℤ (TensorProduct ℤ modTwoCoefficients integerModule) from rfl)).trans
    (TensorProduct.rid ℤ modTwoCoefficients)

/-- The bundled right unitor agrees with the algebraic right unitor on every tensor. -/
private theorem modTwoTensorRid_apply (t : modTwoTensor) :
    modTwoTensorRid t = TensorProduct.rid ℤ modTwoCoefficients t := by
  unfold modTwoTensorRid
  rfl

/-- The algebraic right unitor detects each single-coordinate tensor. -/
@[simp]
theorem rid_modTwoTensorVector (n : ℕ) :
    TensorProduct.rid ℤ modTwoCoefficients (modTwoTensorVector n) = modTwoVector n := by
  simp only [modTwoTensorVector_eq_tmul, TensorProduct.rid_tmul, one_smul]

/-- All coordinates of the tensor detector are given by the single-coordinate formula. -/
theorem rid_modTwoTensorVector_apply (n i : ℕ) :
    TensorProduct.rid ℤ modTwoCoefficients (modTwoTensorVector n) i =
      if n = i then 1 else 0 := by
  rw [rid_modTwoTensorVector, modTwoVector_apply]

/-- Every single-coordinate tensor is nonzero. -/
theorem modTwoTensorVector_ne_zero (n : ℕ) : modTwoTensorVector n ≠ 0 := by
  intro h
  have hi := congrArg modTwoTensorRid h
  rw [map_zero modTwoTensorRid, modTwoTensorRid_apply, rid_modTwoTensorVector] at hi
  exact modTwoVector_ne_zero n hi

/-- Different coefficient positions give different tensors. -/
theorem modTwoTensorVector_ne (n k : ℕ) (h : n ≠ k) :
    modTwoTensorVector n ≠ modTwoTensorVector k := by
  intro heq
  have hi := congrArg (fun t : modTwoTensor ↦ modTwoTensorRid t n) heq
  rw [modTwoTensorRid_apply, modTwoTensorRid_apply, rid_modTwoTensorVector_apply,
    rid_modTwoTensorVector_apply, ite_eq_left rfl, ite_eq_right h.symm] at hi
  exact one_ne_zero hi

/-- A sum of two single-coordinate tensors. -/
noncomputable def modTwoMixedTensor (n k : ℕ) : modTwoTensor :=
  modTwoTensorVector n + modTwoTensorVector k

/-- The right unitor detects the coefficient sum of a two-generator tensor. -/
@[simp]
theorem rid_modTwoMixedTensor (n k : ℕ) :
    TensorProduct.rid ℤ modTwoCoefficients (modTwoMixedTensor n k) =
      modTwoVector n + modTwoVector k := by
  rw [← modTwoTensorRid_apply, modTwoMixedTensor, map_add modTwoTensorRid,
    modTwoTensorRid_apply, modTwoTensorRid_apply, rid_modTwoTensorVector,
    rid_modTwoTensorVector]

/-- A two-generator tensor at different positions has two nonzero detector coordinates. -/
theorem modTwoMixedTensor_coordinates (n k : ℕ) (h : n ≠ k) :
    TensorProduct.rid ℤ modTwoCoefficients (modTwoMixedTensor n k) n = 1 ∧
      TensorProduct.rid ℤ modTwoCoefficients (modTwoMixedTensor n k) k = 1 := by
  constructor
  · have hi := congrArg (fun c : modTwoCoefficients ↦ c n) (rid_modTwoMixedTensor n k)
    have hv := congrArg₂ (fun a b : ZMod 2 ↦ a + b)
      (modTwoVector_apply n n) (modTwoVector_apply k n)
    exact hi.trans ((Finsupp.add_apply (modTwoVector n) (modTwoVector k) n).trans
      (hv.trans (by simp only [ite_eq_right h.symm, add_zero, ite_true])))
  · have hi := congrArg (fun c : modTwoCoefficients ↦ c k) (rid_modTwoMixedTensor n k)
    have hv := congrArg₂ (fun a b : ZMod 2 ↦ a + b)
      (modTwoVector_apply n k) (modTwoVector_apply k k)
    exact hi.trans ((Finsupp.add_apply (modTwoVector n) (modTwoVector k) k).trans
      (hv.trans (by simp only [ite_eq_right h, zero_add, ite_true])))

/-- The algebraic detector has exactly the two indicated support positions. -/
theorem modTwoMixedTensor_support (n k : ℕ) (h : n ≠ k) :
    (TensorProduct.rid ℤ modTwoCoefficients (modTwoMixedTensor n k)).support = {n, k} := by
  have hd : Disjoint (modTwoVector n).support (modTwoVector k).support := by
    simpa only [modTwoVector_support, Finset.disjoint_singleton] using h
  rw [rid_modTwoMixedTensor, Finsupp.support_add_eq hd, modTwoVector_support,
    modTwoVector_support]
  simp

/-- The two-generator tensor at different positions is nonzero. -/
theorem modTwoMixedTensor_ne_zero (n k : ℕ) (h : n ≠ k) :
    modTwoMixedTensor n k ≠ 0 := by
  intro heq
  have hi := congrArg (fun t : modTwoTensor ↦ modTwoTensorRid t n) heq
  rw [map_zero modTwoTensorRid, Finsupp.zero_apply, modTwoTensorRid_apply] at hi
  exact one_ne_zero (((modTwoMixedTensor_coordinates n k h).1).symm.trans hi)

/-- Multiplication by `2` annihilates the nonzero single-coordinate tensors. -/
theorem two_smul_modTwoTensorVector (n : ℕ) : (2 : ℤ) • modTwoTensorVector n = 0 := by
  have ht := @two_smul (R := ℤ) (M := modTwoTensor) inferInstance
    modTwoTensor.toModuleCat.isAddCommGroup.toAddCommMonoid
    modTwoTensor.toModuleCat.isModule (modTwoTensorVector n)
  have hc := @two_smul (R := ℤ) (M := modTwoCoefficients) inferInstance
    modTwoCoefficients.isAddCommGroup.toAddCommMonoid
    modTwoCoefficients.isModule (modTwoVector n)
  apply modTwoTensorRid.injective
  calc
    modTwoTensorRid ((2 : ℤ) • modTwoTensorVector n) =
        modTwoTensorRid (modTwoTensorVector n + modTwoTensorVector n) :=
      congrArg modTwoTensorRid ht
    _ = modTwoTensorRid (modTwoTensorVector n) + modTwoTensorRid (modTwoTensorVector n) :=
      modTwoTensorRid.map_add _ _
    _ = modTwoVector n + modTwoVector n :=
      congrArg₂ (fun c d : modTwoCoefficients ↦ c + d)
        ((modTwoTensorRid_apply _).trans (rid_modTwoTensorVector n))
        ((modTwoTensorRid_apply _).trans (rid_modTwoTensorVector n))
    _ = 0 := hc.symm.trans (two_smul_modTwoCoefficients (modTwoVector n))
    _ = modTwoTensorRid 0 := modTwoTensorRid.map_zero.symm

example (n : ℕ) : (1 : ℤ) • modTwoTensorVector n = modTwoTensorVector n := one_smul ℤ _
example (n : ℕ) : (0 : ℤ) • modTwoTensorVector n = 0 := zero_smul ℤ _
example : modTwoTensorVector 0 ≠ modTwoTensorVector 1 :=
  modTwoTensorVector_ne 0 1 (by norm_num)
example : modTwoMixedTensor 0 1 ≠ 0 := modTwoMixedTensor_ne_zero 0 1 (by norm_num)

-- The scalar action is continuous at bottom, and the canonical tensor object is discrete.
example : (@ContinuousSMul ℤ (modTwoCoefficients ⊗[ℤ] integerModule) _ _
  (⊥ : TopologicalSpace (modTwoCoefficients ⊗[ℤ] integerModule))) :=
  TensorProduct.continuousSMul_bot_of_discrete_right ℤ modTwoCoefficients integerModule
example : (DiscreteTopology modTwoTensor) :=
  TopModuleCat.discreteTopology_tensorLeftObj ℤ modTwoCoefficients integerModule

/-- Projection to the integer factor is continuous for the product topology. -/
theorem continuous_integerReal_fst : Continuous (RingHom.fst ℤ ℝ) := continuous_fst

/-- The integer module restricted along the first projection of `ℤ × ℝ`. -/
noncomputable abbrev integerRealModule : TopModuleCat (ℤ × ℝ) :=
  TopModuleCat.restrictScalarsObj (RingHom.fst ℤ ℝ) continuous_integerReal_fst integerModule

/-- Algebraic regular coefficients for the product ring. -/
noncomputable abbrev integerRealCoefficients : ModuleCat (ℤ × ℝ) :=
  ModuleCat.of (ℤ × ℝ) (ℤ × ℝ)

section ProductModel

/-- The additive group stored in the restricted integer module. -/
noncomputable local instance integerRealModuleAddCommGroup :
    AddCommGroup integerRealModule := integerRealModule.toModuleCat.isAddCommGroup

/-- The product-ring action stored in the restricted integer module. -/
noncomputable local instance integerRealModuleModule :
    Module (ℤ × ℝ) integerRealModule := integerRealModule.toModuleCat.isModule

/-- The canonical one-sided tensor over `ℤ × ℝ`. -/
noncomputable abbrev integerRealTensor : TopModuleCat (ℤ × ℝ) :=
  TopModuleCat.tensorLeftObj (ℤ × ℝ) integerRealCoefficients integerRealModule

/-- The algebraic left unitor on the bundled product-ring tensor module. -/
private noncomputable def integerRealTensorLid :
    integerRealTensor ≃ₗ[ℤ × ℝ] integerRealModule :=
  (LinearEquiv.cast (R := ℤ × ℝ) (M := fun X : ModuleCat (ℤ × ℝ) ↦ (X : Type))
    (show integerRealTensor.toModuleCat =
      @ModuleCat.of (ℤ × ℝ) _
        (TensorProduct (ℤ × ℝ) integerRealCoefficients integerRealModule)
        integerRealTensor.toModuleCat.isAddCommGroup
        integerRealTensor.toModuleCat.isModule from rfl)).trans
    (TensorProduct.lid (ℤ × ℝ) integerRealModule)

/-- The bundled left unitor agrees with the algebraic left unitor on every tensor. -/
private theorem integerRealTensorLid_apply (t : integerRealTensor) :
    integerRealTensorLid t = TensorProduct.lid (ℤ × ℝ) integerRealModule t := by
  unfold integerRealTensorLid
  rfl

/-- The restricted action on every scalar and every module element. -/
@[simp]
theorem integerRealModule_smul (r : ℤ × ℝ) (m : integerRealModule) :
    r • m = (show integerRealModule from r.1 * (m : ℤ)) := by
  simpa only [RingHom.coe_fst, smul_eq_mul] using
    TopModuleCat.restrictScalarsObj_smul (RingHom.fst ℤ ℝ) continuous_integerReal_fst
      integerModule r (show integerModule from m)

/-- The underlying module is Mathlib's restriction along the first projection. -/
theorem integerRealModule_toModuleCat :
    integerRealModule.toModuleCat =
      (ModuleCat.restrictScalars (RingHom.fst ℤ ℝ)).obj integerModule.toModuleCat :=
  TopModuleCat.restrictScalarsObj_toModuleCat (RingHom.fst ℤ ℝ)
    continuous_integerReal_fst integerModule

/-- The topology is exactly the original integer module topology. -/
theorem integerRealModule_topologicalSpace :
    integerRealModule.topologicalSpace = integerModule.topologicalSpace :=
  TopModuleCat.restrictScalarsObj_topologicalSpace (RingHom.fst ℤ ℝ)
    continuous_integerReal_fst integerModule

/-- Restriction retains the discrete integer topology. -/
theorem discreteTopology_integerRealModule : DiscreteTopology integerRealModule :=
  inferInstance

/-- The full scalar action is jointly continuous, using the restriction bundle. -/
theorem continuous_integerRealModule_smul :
    Continuous (fun p : (ℤ × ℝ) × integerRealModule ↦ p.1 • p.2) :=
  integerRealModule.continuousSMul.continuous_smul

/-- Joint continuity in the multiplication formula, for all independent scalar
and module inputs. The real coordinate is ignored by the first projection. -/
theorem continuous_integerRealModule_action :
    Continuous (fun p : (ℤ × ℝ) × integerRealModule ↦ p.1.1 * (p.2 : ℤ)) := by
  exact continuous_integerRealModule_smul.congr
    (fun p ↦ integerRealModule_smul p.1 p.2)

/-- The product scalar ring is not discrete: an open singleton would project
to an open singleton in the usual real topology. -/
theorem integerRealScalars_not_discrete : ¬ DiscreteTopology (ℤ × ℝ) := by
  intro h
  let : DiscreteTopology (ℤ × ℝ) := h
  have hopen : IsOpen ({((0 : ℤ), (0 : ℝ))} : Set (ℤ × ℝ)) := isOpen_discrete _
  have hreal : IsOpen ({(0 : ℝ)} : Set ℝ) := by
    simpa only [Set.image_singleton] using isOpenMap_snd _ hopen
  exact not_isOpen_singleton (0 : ℝ) hreal

/-- Varying the integer scalar and the module element changes the action;
the real scalar coordinate can vary independently. -/
theorem integerRealModule_action_values (x : ℝ) :
    ((0, x) : ℤ × ℝ) • (1 : integerRealModule) = 0 ∧
      ((1, x) : ℤ × ℝ) • (1 : integerRealModule) = 1 ∧
      ((1, x) : ℤ × ℝ) • (0 : integerRealModule) = 0 := by
  exact ⟨(integerRealModule_smul (0, x) 1).trans (zero_mul (1 : ℤ)),
    (integerRealModule_smul (1, x) 1).trans (one_mul (1 : ℤ)),
    (integerRealModule_smul (1, x) 0).trans (one_mul (0 : ℤ))⟩

example : ((0, 0) : ℤ × ℝ) ≠ (1, 0) := by
  intro h
  exact zero_ne_one (congrArg Prod.fst h)
example : (0 : integerRealModule) ≠ 1 := zero_ne_one
example (x : ℝ) :
    ((0, x) : ℤ × ℝ) • (1 : integerRealModule) ≠
      ((1, x) : ℤ × ℝ) • (1 : integerRealModule) := by
  intro h
  have hvalues := integerRealModule_action_values x
  exact zero_ne_one (hvalues.1.symm.trans (h.trans hvalues.2.1))
example (x : ℝ) :
    ((1, x) : ℤ × ℝ) • (0 : integerRealModule) ≠
      ((1, x) : ℤ × ℝ) • (1 : integerRealModule) := by
  intro h
  have hvalues := integerRealModule_action_values x
  exact zero_ne_one (hvalues.2.2.symm.trans (h.trans hvalues.2.1))

-- The dictionaries and laws come from restriction, not a replacement action.
noncomputable example : AddCommGroup integerRealCoefficients :=
  integerRealCoefficients.isAddCommGroup
noncomputable example : Module (ℤ × ℝ) integerRealCoefficients := integerRealCoefficients.isModule
noncomputable example : AddCommGroup integerRealModule := integerRealModule.isAddCommGroup
noncomputable example : Module (ℤ × ℝ) integerRealModule := integerRealModule.isModule
example : IsTopologicalAddGroup integerRealModule := integerRealModule.isTopologicalAddGroup
example : ContinuousAdd integerRealModule := inferInstance
example : ContinuousSMul (ℤ × ℝ) integerRealModule := integerRealModule.continuousSMul
example : DiscreteTopology integerRealModule := discreteTopology_integerRealModule
example (r s : ℤ × ℝ) (m : integerRealModule) : (r * s) • m = r • (s • m) :=
  mul_smul r s m
example (r : ℤ × ℝ) (m n : integerRealModule) : r • (m + n) = r • m + r • n :=
  smul_add r m n
example (r s : ℤ × ℝ) (m : integerRealModule) : (r + s) • m = r • m + s • m :=
  add_smul r s m
example (m : integerRealModule) : (1 : ℤ × ℝ) • m = m := one_smul _ m
noncomputable example : AddCommGroup integerRealTensor := integerRealTensor.isAddCommGroup
noncomputable example : Module (ℤ × ℝ) integerRealTensor := integerRealTensor.isModule
example : IsTopologicalAddGroup integerRealTensor := integerRealTensor.isTopologicalAddGroup
example : ContinuousAdd integerRealTensor := inferInstance
example : ContinuousSMul (ℤ × ℝ) integerRealTensor := integerRealTensor.continuousSMul

/-- The output joint action is the one stored in the canonical tensor bundle. -/
theorem continuous_integerRealTensor_smul :
    Continuous (fun p : (ℤ × ℝ) × integerRealTensor ↦ p.1 • p.2) :=
  integerRealTensor.continuousSMul.continuous_smul

/-- The fixed-coefficient generator evaluated at an arbitrary integer. -/
noncomputable def integerRealTensorValue (r : ℤ × ℝ) (m : integerRealModule) :
    integerRealTensor :=
  TopModuleCat.tensorGenerator (ℤ × ℝ) integerRealCoefficients integerRealModule r m

/-- Generator values are the unchanged algebraic pure tensors. -/
@[simp]
theorem integerRealTensorValue_eq_tmul (r : ℤ × ℝ) (m : integerRealModule) :
    integerRealTensorValue r m = r ⊗ₜ[ℤ × ℝ] m :=
  TopModuleCat.tensorGenerator_apply (ℤ × ℝ) integerRealCoefficients integerRealModule r m

/-- The algebraic left unitor detects every generator value using the restricted action. -/
@[simp]
theorem lid_integerRealTensorValue (r : ℤ × ℝ) (m : integerRealModule) :
    TensorProduct.lid (ℤ × ℝ) integerRealModule (integerRealTensorValue r m) =
      (show integerRealModule from r.1 * (m : ℤ)) := by
  exact (congrArg (TensorProduct.lid (ℤ × ℝ) integerRealModule)
    (integerRealTensorValue_eq_tmul r m)).trans
      ((TensorProduct.lid_tmul (R := ℤ × ℝ) (M := integerRealModule) m r).trans
        (integerRealModule_smul r m))

/-- The algebraic detector computes arbitrary sums of generator values. -/
theorem lid_integerRealTensorValue_add (r s : ℤ × ℝ) (m n : integerRealModule) :
    TensorProduct.lid (ℤ × ℝ) integerRealModule
      (integerRealTensorValue r m + integerRealTensorValue s n) =
        (show integerRealModule from r.1 * (m : ℤ) + s.1 * (n : ℤ)) := by
  rw [← integerRealTensorLid_apply, map_add integerRealTensorLid,
    integerRealTensorLid_apply, integerRealTensorLid_apply, lid_integerRealTensorValue,
    lid_integerRealTensorValue]

/-- A nonzero pure tensor is detected by `1` in the right module. -/
theorem integerRealTensorValue_one_ne_zero : integerRealTensorValue (1, 0) 1 ≠ 0 := by
  intro h
  have hv : TensorProduct.lid (ℤ × ℝ) integerRealModule
      (integerRealTensorValue (1, 0) 1) = (1 : integerRealModule) :=
    (lid_integerRealTensorValue (1, 0) 1).trans (one_mul (1 : ℤ))
  have h0 : TensorProduct.lid (ℤ × ℝ) integerRealModule (0 : integerRealTensor) = 0 :=
    (TensorProduct.lid (ℤ × ℝ) integerRealModule).map_zero
  have hi : (1 : integerRealModule) = 0 :=
    hv.symm.trans ((congrArg (TensorProduct.lid (ℤ × ℝ) integerRealModule) h).trans h0)
  exact one_ne_zero hi

/-- The second pure tensor is detected by the nonzero integer `2`. -/
theorem integerRealTensorValue_two_ne_zero : integerRealTensorValue (2, 1) 1 ≠ 0 := by
  intro h
  have hv : TensorProduct.lid (ℤ × ℝ) integerRealModule
      (integerRealTensorValue (2, 1) 1) = (2 : integerRealModule) :=
    (lid_integerRealTensorValue (2, 1) 1).trans (mul_one (2 : ℤ))
  have h0 : TensorProduct.lid (ℤ × ℝ) integerRealModule (0 : integerRealTensor) = 0 :=
    (TensorProduct.lid (ℤ × ℝ) integerRealModule).map_zero
  have hi : (2 : ℤ) = 0 :=
    hv.symm.trans ((congrArg (TensorProduct.lid (ℤ × ℝ) integerRealModule) h).trans h0)
  norm_num at hi

/-- The detector distinguishes two nonzero generator values. -/
theorem integerRealTensorValue_one_ne_two :
    integerRealTensorValue (1, 0) 1 ≠ integerRealTensorValue (2, 1) 1 := by
  intro h
  have hv1 : TensorProduct.lid (ℤ × ℝ) integerRealModule
      (integerRealTensorValue (1, 0) 1) = (1 : integerRealModule) :=
    (lid_integerRealTensorValue (1, 0) 1).trans (one_mul (1 : ℤ))
  have hv2 : TensorProduct.lid (ℤ × ℝ) integerRealModule
      (integerRealTensorValue (2, 1) 1) = (2 : integerRealModule) :=
    (lid_integerRealTensorValue (2, 1) 1).trans (mul_one (2 : ℤ))
  have hi : (1 : ℤ) = 2 :=
    hv1.symm.trans ((congrArg (TensorProduct.lid (ℤ × ℝ) integerRealModule) h).trans hv2)
  norm_num at hi

/-- A mixed sum has detector value `3`, so it cannot vanish. -/
theorem integerRealTensorValue_mixed_ne_zero :
    integerRealTensorValue (1, 0) 1 + integerRealTensorValue (2, 1) 1 ≠ 0 := by
  intro h
  have hv : TensorProduct.lid (ℤ × ℝ) integerRealModule
      (integerRealTensorValue (1, 0) 1 + integerRealTensorValue (2, 1) 1) =
        (3 : integerRealModule) :=
    (lid_integerRealTensorValue_add (1, 0) (2, 1) 1 1).trans
      (by norm_num : (1 : ℤ) * 1 + 2 * 1 = 3)
  have h0 : TensorProduct.lid (ℤ × ℝ) integerRealModule (0 : integerRealTensor) = 0 :=
    (TensorProduct.lid (ℤ × ℝ) integerRealModule).map_zero
  have hi : (3 : ℤ) = 0 :=
    hv.symm.trans ((congrArg (TensorProduct.lid (ℤ × ℝ) integerRealModule) h).trans h0)
  norm_num at hi

-- These nondiscrete scalars act continuously at bottom; the canonical tensor object is discrete.
example : (@ContinuousSMul (ℤ × ℝ) (integerRealCoefficients ⊗[ℤ × ℝ] integerRealModule) _ _
  (⊥ : TopologicalSpace (integerRealCoefficients ⊗[ℤ × ℝ] integerRealModule))) :=
  TensorProduct.continuousSMul_bot_of_discrete_right (ℤ × ℝ)
    integerRealCoefficients integerRealModule
example : (DiscreteTopology integerRealTensor) :=
  TopModuleCat.discreteTopology_tensorLeftObj (ℤ × ℝ)
    integerRealCoefficients integerRealModule

end ProductModel

end DiscreteTensorExamples
