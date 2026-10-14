/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicDirectLimits.Topology.TensorProduct
public import AlgebraicDirectLimits.Topology.TensorProduct.Prod
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Topology.Algebra.Group.ZPow
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
public import Mathlib.Topology.Instances.Int
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Order.DenselyOrdered

/-!
# Torsion and infinitely generated coefficient blocks

The scalar ring is `ℤ` with its usual topology. The coefficients are
`(ZMod 2 × ZMod 2) × (ℕ →₀ ℤ)`, with their canonical algebraic structures and
no chosen coefficient topology. The right module is `ℤ × ℝ` with its original
product topology and coordinatewise integer action. It is not discrete.

The torsion block has two independent nonzero tensor directions detected by the
integer right coordinate. Its real right coordinate is annihilated: divisibility
of `ℝ` by two and two-torsion of the coefficients force those tensors to vanish.
For rank-one `ZMod 2` there would be only one nonzero tensor direction; the
rank-two block here permits distinct nonzero values with a nonzero mixed sum.
The Finsupp block detects every real coordinate independently, as well as the
complementary integer right coordinate.

The maps into and out of the combined tensor use `tensorMapCLM` with the
algebraic product inclusions and projections. The algebraic detectors use only
Mathlib's tensor map, unitors and Finsupp evaluations. No topology is asserted
on the detector target coefficients. These controls do not use a continuous
product equivalence.

## Limitations

The laws using `TopModuleCat.tensorProdLeft` describe distribution and its inverse.
The stored module structures and algebraic detector controls do
not use these laws or the continuous product equivalence.

## References

The product equivalence is Mathlib's construction by Eric Wieser. The tensor
maps and unitors are due to Kenny Lau and Mario Carneiro, and Finsupp evaluations
to Johannes Hölzl and Kim Morrison. Integer module and scalar-action bridges
use the work of Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl and Mario
Carneiro; integer-action continuity also uses Patrick Massot's work. ZMod is
due to Chris Hughes, and the torsion-free module API to Yaël Dillies. The
one-sided topology follows the Continuous Group Cohomology development,
including Beacon's original work, and Mathlib's Richard Hill and Andrew Yang.
The tensor-map and stored-module approaches follow the existing Algebraic
Direct Limits development by Formal Frontier Agents. These elementary specimen
calculations are original Formal Frontier contributions developed with AI
assistance.
-/

@[expose] public section

open scoped TensorProduct

namespace CoefficientTensorProdExamples

/-- Rank-two two-torsion coefficients with the canonical integer module. -/
abbrev torsionCoefficients : ModuleCat ℤ :=
  @ModuleCat.of ℤ _ (ZMod 2 × ZMod 2) inferInstance Prod.instModule

/-- Infinitely generated integer coefficients with finite support. -/
noncomputable abbrev finsuppCoefficients : ModuleCat ℤ :=
  @ModuleCat.of ℤ _ (ℕ →₀ ℤ) inferInstance (Finsupp.module ℕ ℤ)

/-- The algebraic product of the two stored coefficient modules. -/
noncomputable abbrev productCoefficients : ModuleCat ℤ :=
  @ModuleCat.of ℤ _ (torsionCoefficients × finsuppCoefficients)
    inferInstance Prod.instModule

/-- Integer-real pairs with the original product topology and integer action. -/
abbrev rightModule : TopModuleCat ℤ := by
  letI : ContinuousSMul ℤ ℤ := AddGroup.continuousSMul_int
  letI : ContinuousSMul ℤ ℝ := AddGroup.continuousSMul_int
  exact @TopModuleCat.of ℤ _ _ (ℤ × ℝ) inferInstance Prod.instModule
    inferInstance inferInstance Prod.continuousSMul

/-- The stored additive group of the right module, registered only in this scope. -/
local instance rightModuleGroup : AddCommGroup rightModule :=
  rightModule.toModuleCat.isAddCommGroup

/-- The stored integer module of the right module, registered only in this scope. -/
local instance rightModuleModule : Module ℤ rightModule :=
  rightModule.toModuleCat.isModule

/-- The canonical coinduced tensor for the torsion block. -/
noncomputable abbrev torsionTensor : TopModuleCat ℤ :=
  TopModuleCat.tensorLeftObj ℤ torsionCoefficients rightModule

/-- The canonical coinduced tensor for the Finsupp block. -/
noncomputable abbrev finsuppTensor : TopModuleCat ℤ :=
  TopModuleCat.tensorLeftObj ℤ finsuppCoefficients rightModule

/-- The canonical coinduced tensor for the coefficient product. -/
noncomputable abbrev productTensor : TopModuleCat ℤ :=
  TopModuleCat.tensorLeftObj ℤ productCoefficients rightModule

/-- The ordinary product of the two canonical tensor objects. -/
noncomputable abbrev tensorOutput : TopModuleCat ℤ :=
  @TopModuleCat.of ℤ _ _ (torsionTensor × finsuppTensor)
    inferInstance Prod.instModule inferInstance inferInstance Prod.continuousSMul

/-- The stored integer action on every integer-real pair. -/
theorem rightModule_smul (r a : ℤ) (x : ℝ) :
    r • ((a, x) : rightModule) = ((r * a, (r : ℝ) * x) : rightModule) := by
  have h := @int_smul_eq_zsmul rightModule rightModuleGroup
    rightModuleModule r ((a, x) : rightModule)
  have hcoords : ((r • a, r • x) : ℤ × ℝ) = (r * a, (r : ℝ) * x) :=
    Prod.ext (Int.zsmul_eq_mul r a) (zsmul_eq_mul x r)
  exact h.trans hcoords

/-- Full joint continuity for the stored scalar action. -/
theorem rightModule_continuous_smul :
    Continuous (fun p : ℤ × rightModule ↦ p.1 • p.2) :=
  rightModule.continuousSMul.continuous_smul

/-- Joint continuity expressed by the characteristic action formula. -/
theorem rightModule_continuous_action :
    Continuous (fun p : ℤ × rightModule ↦
      ((p.1 * p.2.1, (p.1 : ℝ) * p.2.2) : rightModule)) := by
  exact rightModule_continuous_smul.congr
    (fun p ↦ rightModule_smul p.1 p.2.1 p.2.2)

/-- Addition uses the original product topology. -/
theorem rightModule_continuous_add :
    Continuous (fun p : rightModule × rightModule ↦ p.1 + p.2) := continuous_add

/-- The stored action satisfies the module laws for all inputs. -/
theorem rightModule_module_laws (r s : ℤ) (m n : rightModule) :
    (0 : ℤ) • m = 0 ∧ (1 : ℤ) • m = m ∧
    (r + s) • m = r • m + s • m ∧ (r * s) • m = r • (s • m) ∧
    r • (m + n) = r • m + r • n :=
  ⟨zero_smul ℤ m, one_smul ℤ m, add_smul r s m, mul_smul r s m, smul_add r m n⟩

/-- Each canonical tensor and their ordinary product has joint scalar continuity. -/
theorem tensorObjects_continuous_smul :
    Continuous (fun p : ℤ × torsionTensor ↦ p.1 • p.2) ∧
    Continuous (fun p : ℤ × finsuppTensor ↦ p.1 • p.2) ∧
    Continuous (fun p : ℤ × productTensor ↦ p.1 • p.2) ∧
    Continuous (fun p : ℤ × tensorOutput ↦ p.1 • p.2) :=
  ⟨torsionTensor.continuousSMul.continuous_smul,
    finsuppTensor.continuousSMul.continuous_smul,
    productTensor.continuousSMul.continuous_smul,
    tensorOutput.continuousSMul.continuous_smul⟩

/-- Each canonical tensor and their ordinary product has continuous addition. -/
theorem tensorObjects_continuous_add :
    Continuous (fun p : torsionTensor × torsionTensor ↦ p.1 + p.2) ∧
    Continuous (fun p : finsuppTensor × finsuppTensor ↦ p.1 + p.2) ∧
    Continuous (fun p : productTensor × productTensor ↦ p.1 + p.2) ∧
    Continuous (fun p : tensorOutput × tensorOutput ↦ p.1 + p.2) :=
  ⟨continuous_add, continuous_add, continuous_add, continuous_add⟩

/-- The two right coordinates and scalars one and two vary independently. -/
theorem rightModule_action_controls :
    (1 : ℤ) • ((1, 0) : rightModule) = (1, 0) ∧
    (2 : ℤ) • ((1, 0) : rightModule) = (2, 0) ∧
    (1 : ℤ) • ((0, 1) : rightModule) = (0, 1) ∧
    (2 : ℤ) • ((0, 1) : rightModule) = (0, 2) := by
  simp only [rightModule_smul]
  norm_num

/-- The original right module is not discrete. -/
theorem rightModule_not_discrete : ¬ DiscreteTopology rightModule := by
  intro h
  let : DiscreteTopology rightModule := h
  have hc : Continuous (fun x : ℝ ↦ ((0, x) : rightModule)) :=
    continuous_const.prodMk continuous_id
  have hi : Function.Injective (fun x : ℝ ↦ ((0, x) : rightModule)) := by
    intro x y hxy
    exact congrArg Prod.snd hxy
  let : DiscreteTopology ℝ := DiscreteTopology.of_continuous_injective hc hi
  have hs : Subsingleton ℝ := DenselyOrdered.subsingleton_of_discreteTopology
  exact (zero_ne_one : (0 : ℝ) ≠ 1) (hs.elim 0 1)

/-- Every stored torsion coefficient is annihilated by two. -/
theorem torsionCoefficients_two_smul (c : torsionCoefficients) : (2 : ℤ) • c = 0 := by
  have hc : (2 : ℤ) • c = c + c :=
    @two_smul ℤ torsionCoefficients inferInstance
      torsionCoefficients.isAddCommGroup.toAddCommMonoid torsionCoefficients.isModule c
  rw [hc]
  have h2 : (2 : ZMod 2) = 0 := by decide
  apply Prod.ext
  · change c.1 + c.1 = 0
    rw [← two_mul, h2, zero_mul]
  · change c.2 + c.2 = 0
    rw [← two_mul, h2, zero_mul]

/-- The first torsion coefficient. -/
def c0 : torsionCoefficients := (1, 0)

/-- The second torsion coefficient. -/
def c1 : torsionCoefficients := (0, 1)

/-- Both coefficient directions and their sum are nonzero and distinct. -/
theorem coefficient_controls : c0 ≠ 0 ∧ c1 ≠ 0 ∧ c0 ≠ c1 ∧ c0 + c1 ≠ 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    have := congrArg Prod.fst h
    simp [c0] at this
  · intro h
    have := congrArg Prod.snd h
    simp [c1] at this
  · intro h
    have := congrArg Prod.fst h
    simp [c0, c1] at this
  · intro h
    have := congrArg Prod.fst h
    simp [c0, c1] at this

/-- The torsion block is not free over the integer domain. -/
theorem torsionCoefficients_not_free : ¬ Module.Free ℤ torsionCoefficients := by
  intro h
  let : Module.Free ℤ torsionCoefficients := h
  have hz := (smul_eq_zero : (2 : ℤ) • c0 = 0 ↔ (2 : ℤ) = 0 ∨ c0 = 0).mp
    (torsionCoefficients_two_smul c0)
  rcases hz with h2 | hc
  · norm_num at h2
  · exact coefficient_controls.1 hc

/-- The Finsupp block is not finitely generated as an integer module. -/
theorem finsuppCoefficients_not_finite : ¬ Module.Finite ℤ finsuppCoefficients := by
  intro h
  have hi : Subsingleton ℤ ∨ Finite ℕ := Module.finite_finsupp_self_iff.mp h
  rcases hi with hz | hn
  · exact (zero_ne_one : (0 : ℤ) ≠ 1) (hz.elim 0 1)
  · exact @Infinite.not_finite ℕ inferInstance hn

/-- The whole coefficient product is not finitely generated. -/
theorem productCoefficients_not_finite : ¬ Module.Finite ℤ productCoefficients := by
  intro h
  let : Module.Finite ℤ productCoefficients := h
  apply finsuppCoefficients_not_finite
  exact Module.Finite.of_surjective
    (LinearMap.snd ℤ torsionCoefficients finsuppCoefficients)
    (fun d ↦ ⟨(0, d), rfl⟩)

/-- The product coefficients retain a nonzero two-torsion vector and are not free. -/
theorem productCoefficients_not_free : ¬ Module.Free ℤ productCoefficients := by
  intro h
  let : Module.Free ℤ productCoefficients := h
  let q : productCoefficients := (c0, 0)
  have hq : (2 : ℤ) • q = 0 := by
    change ((2 : ℤ) • c0, (2 : ℤ) • (0 : finsuppCoefficients)) = (0, 0)
    rw [torsionCoefficients_two_smul, smul_zero]
  have hz := (smul_eq_zero : (2 : ℤ) • q = 0 ↔ (2 : ℤ) = 0 ∨ q = 0).mp hq
  rcases hz with h2 | hq0
  · norm_num at h2
  · exact coefficient_controls.1 (congrArg Prod.fst hq0)

/-- The algebraic detector pairing the torsion coefficient with the integer right
coordinate, followed by the right tensor unit. -/
noncomputable def torsionDetector : torsionTensor →ₗ[ℤ] torsionCoefficients :=
  (TensorProduct.rid ℤ torsionCoefficients).toLinearMap.comp
    (TensorProduct.map (LinearMap.id : torsionCoefficients →ₗ[ℤ] torsionCoefficients)
      (LinearMap.fst ℤ ℤ ℝ : rightModule →ₗ[ℤ] ℤ))

private theorem torsionDetector_apply (t : torsionTensor) :
    torsionDetector t = TensorProduct.rid ℤ torsionCoefficients
      (TensorProduct.map (LinearMap.id : torsionCoefficients →ₗ[ℤ] torsionCoefficients)
        (LinearMap.fst ℤ ℤ ℝ : rightModule →ₗ[ℤ] ℤ) t) := rfl

/-- The integer detector's formula for all coefficients and right inputs. -/
theorem torsionDetector_tmul (c : torsionCoefficients) (a : ℤ) (x : ℝ) :
    torsionDetector (c ⊗ₜ[ℤ] ((a, x) : rightModule)) = a • c := by
  have ha := torsionDetector_apply
    (c ⊗ₜ[ℤ] ((a, x) : rightModule) : torsionTensor)
  have hm : TensorProduct.map
      (LinearMap.id : torsionCoefficients →ₗ[ℤ] torsionCoefficients)
      (LinearMap.fst ℤ ℤ ℝ : rightModule →ₗ[ℤ] ℤ)
      (c ⊗ₜ[ℤ] ((a, x) : rightModule) : torsionTensor) =
        (c ⊗ₜ[ℤ] a : TensorProduct ℤ torsionCoefficients ℤ) :=
    TensorProduct.map_tmul
      (LinearMap.id : torsionCoefficients →ₗ[ℤ] torsionCoefficients)
      (LinearMap.fst ℤ ℤ ℝ : rightModule →ₗ[ℤ] ℤ) c ((a, x) : rightModule)
  exact ha.trans ((congrArg (TensorProduct.rid ℤ torsionCoefficients) hm).trans
    (TensorProduct.rid_tmul c a))

/-- The algebraic detector pairing Finsupp evaluation at `i` with the real right
coordinate, followed by the left tensor unit. -/
noncomputable def realDetector (i : ℕ) : finsuppTensor →ₗ[ℤ] ℝ :=
  (TensorProduct.lid ℤ ℝ).toLinearMap.comp
    (TensorProduct.map (Finsupp.lapply i : finsuppCoefficients →ₗ[ℤ] ℤ)
      (LinearMap.snd ℤ ℤ ℝ : rightModule →ₗ[ℤ] ℝ))

private theorem realDetector_apply (i : ℕ) (t : finsuppTensor) :
    realDetector i t = TensorProduct.lid ℤ ℝ
      (TensorProduct.map (Finsupp.lapply i : finsuppCoefficients →ₗ[ℤ] ℤ)
        (LinearMap.snd ℤ ℤ ℝ : rightModule →ₗ[ℤ] ℝ) t) := rfl

/-- Every Finsupp evaluation and every right input obey the real detector formula. -/
theorem realDetector_tmul (i : ℕ) (d : finsuppCoefficients) (a : ℤ) (x : ℝ) :
    realDetector i (d ⊗ₜ[ℤ] ((a, x) : rightModule)) = (d i : ℝ) * x := by
  have ha := realDetector_apply i
    (d ⊗ₜ[ℤ] ((a, x) : rightModule) : finsuppTensor)
  have hm : TensorProduct.map
      (Finsupp.lapply i : finsuppCoefficients →ₗ[ℤ] ℤ)
      (LinearMap.snd ℤ ℤ ℝ : rightModule →ₗ[ℤ] ℝ)
      (d ⊗ₜ[ℤ] ((a, x) : rightModule) : finsuppTensor) =
        ((d i : ℤ) ⊗ₜ[ℤ] x : TensorProduct ℤ ℤ ℝ) :=
    TensorProduct.map_tmul
      (Finsupp.lapply i : finsuppCoefficients →ₗ[ℤ] ℤ)
      (LinearMap.snd ℤ ℤ ℝ : rightModule →ₗ[ℤ] ℝ) d ((a, x) : rightModule)
  exact ha.trans ((congrArg (TensorProduct.lid ℤ ℝ) hm).trans
    ((TensorProduct.lid_tmul x (d i)).trans (zsmul_eq_mul x (d i))))

/-- The algebraic detector pairing Finsupp evaluation at `i` with the integer right
coordinate, followed by the left tensor unit. -/
noncomputable def integerDetector (i : ℕ) : finsuppTensor →ₗ[ℤ] ℤ :=
  (TensorProduct.lid ℤ ℤ).toLinearMap.comp
    (TensorProduct.map (Finsupp.lapply i : finsuppCoefficients →ₗ[ℤ] ℤ)
      (LinearMap.fst ℤ ℤ ℝ : rightModule →ₗ[ℤ] ℤ))

private theorem integerDetector_apply (i : ℕ) (t : finsuppTensor) :
    integerDetector i t = TensorProduct.lid ℤ ℤ
      (TensorProduct.map (Finsupp.lapply i : finsuppCoefficients →ₗ[ℤ] ℤ)
        (LinearMap.fst ℤ ℤ ℝ : rightModule →ₗ[ℤ] ℤ) t) := rfl

/-- The complementary integer detector also applies to every coefficient and input. -/
theorem integerDetector_tmul (i : ℕ) (d : finsuppCoefficients) (a : ℤ) (x : ℝ) :
    integerDetector i (d ⊗ₜ[ℤ] ((a, x) : rightModule)) = d i * a := by
  have ha := integerDetector_apply i
    (d ⊗ₜ[ℤ] ((a, x) : rightModule) : finsuppTensor)
  have hm : TensorProduct.map
      (Finsupp.lapply i : finsuppCoefficients →ₗ[ℤ] ℤ)
      (LinearMap.fst ℤ ℤ ℝ : rightModule →ₗ[ℤ] ℤ)
      (d ⊗ₜ[ℤ] ((a, x) : rightModule) : finsuppTensor) =
        ((d i : ℤ) ⊗ₜ[ℤ] a : TensorProduct ℤ ℤ ℤ) :=
    TensorProduct.map_tmul
      (Finsupp.lapply i : finsuppCoefficients →ₗ[ℤ] ℤ)
      (LinearMap.fst ℤ ℤ ℝ : rightModule →ₗ[ℤ] ℤ) d ((a, x) : rightModule)
  exact ha.trans ((congrArg (TensorProduct.lid ℤ ℤ) hm).trans
    ((TensorProduct.lid_tmul a (d i)).trans (Int.zsmul_eq_mul (d i) a)))

/-- The first tensor direction in the torsion block. -/
noncomputable def u0 : torsionTensor := c0 ⊗ₜ[ℤ] ((1, 0) : rightModule)

/-- The second tensor direction in the torsion block. -/
noncomputable def u1 : torsionTensor := c1 ⊗ₜ[ℤ] ((1, 0) : rightModule)

/-- The detector distinguishes both torsion directions and their mixed sum. -/
theorem torsionTensor_controls :
    u0 ≠ 0 ∧ u1 ≠ 0 ∧ u0 ≠ u1 ∧ u0 + u1 ≠ 0 := by
  have h0 : torsionDetector u0 = c0 := (torsionDetector_tmul c0 1 0).trans (one_smul ℤ c0)
  have h1 : torsionDetector u1 = c1 := (torsionDetector_tmul c1 1 0).trans (one_smul ℤ c1)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    exact coefficient_controls.1 (h0.symm.trans (by rw [h, map_zero]))
  · intro h
    exact coefficient_controls.2.1 (h1.symm.trans (by rw [h, map_zero]))
  · intro h
    exact coefficient_controls.2.2.1 (h0.symm.trans ((congrArg torsionDetector h).trans h1))
  · intro h
    apply coefficient_controls.2.2.2
    have hi := congrArg torsionDetector h
    simpa only [map_add, h0, h1, map_zero] using hi

/-- Two annihilates every pure tensor in the torsion block, for its stored action. -/
theorem torsionTensor_two_smul (c : torsionCoefficients) (m : rightModule) :
    (2 : ℤ) • (c ⊗ₜ[ℤ] m : torsionTensor) = 0 := by
  have ht : (2 : ℤ) • (c ⊗ₜ[ℤ] m : torsionTensor) =
      (c ⊗ₜ[ℤ] m : torsionTensor) + c ⊗ₜ[ℤ] m :=
    @two_smul ℤ torsionTensor inferInstance
      torsionTensor.toModuleCat.isAddCommGroup.toAddCommMonoid
      torsionTensor.toModuleCat.isModule (c ⊗ₜ[ℤ] m : torsionTensor)
  have hc : c + c = 0 :=
    (@two_smul ℤ torsionCoefficients inferInstance
      torsionCoefficients.isAddCommGroup.toAddCommMonoid
      torsionCoefficients.isModule c).symm.trans (torsionCoefficients_two_smul c)
  rw [ht, ← TensorProduct.add_tmul, hc, TensorProduct.zero_tmul]

/-- Real-only right inputs vanish in the torsion block. -/
theorem torsionTensor_real_annihilated (c : torsionCoefficients) (x : ℝ) :
    (c ⊗ₜ[ℤ] ((0, x) : rightModule) : torsionTensor) = 0 := by
  have hx : (2 : ℤ) • ((0, x / 2) : rightModule) = ((0, x) : rightModule) := by
    rw [rightModule_smul]
    ext <;> norm_num
    ring
  calc
    c ⊗ₜ[ℤ] ((0, x) : rightModule) =
        c ⊗ₜ[ℤ] ((2 : ℤ) • ((0, x / 2) : rightModule)) := congrArg (fun m ↦ c ⊗ₜ[ℤ] m) hx.symm
    _ = ((2 : ℤ) • c) ⊗ₜ[ℤ] ((0, x / 2) : rightModule) :=
      (TensorProduct.smul_tmul (2 : ℤ) c ((0, x / 2) : rightModule)).symm
    _ = 0 := by rw [torsionCoefficients_two_smul, TensorProduct.zero_tmul]

/-- A real input in the Finsupp direction indexed by `n`. -/
noncomputable def v (n : ℕ) (x : ℝ) : finsuppTensor :=
  (Finsupp.single n 1 : finsuppCoefficients) ⊗ₜ[ℤ] ((0, x) : rightModule)

/-- All coordinates of every real Finsupp tensor are evaluated explicitly. -/
theorem realDetector_v (i n : ℕ) (x : ℝ) :
    realDetector i (v n x) = if i = n then x else 0 := by
  classical
  rw [v, realDetector_tmul]
  by_cases h : i = n
  · subst i
    simp
  · simp [h]

/-- A nonzero real input yields a nonzero tensor at every index. -/
theorem v_ne_zero (n : ℕ) {x : ℝ} (hx : x ≠ 0) : v n x ≠ 0 := by
  intro h
  have hi := congrArg (realDetector n) h
  apply hx
  simpa only [realDetector_v, ite_true, map_zero] using hi

/-- Different real inputs at one index give different tensor values. -/
theorem v_ne_of_real_ne (n : ℕ) {x y : ℝ} (hxy : x ≠ y) : v n x ≠ v n y := by
  intro h
  have hi := congrArg (realDetector n) h
  exact hxy (by simpa only [realDetector_v, ite_true] using hi)

/-- A nonzero value at one index differs from every value at a distinct index. -/
theorem v_ne_of_index_ne {n k : ℕ} (hnk : n ≠ k) {x y : ℝ}
    (hx : x ≠ 0) : v n x ≠ v k y := by
  intro h
  have hi := congrArg (realDetector n) h
  apply hx
  simpa only [realDetector_v, ite_true, ite_eq_right hnk] using hi

/-- A mixed Finsupp tensor retains both independently supplied real coordinates. -/
theorem realDetector_mixed {n k : ℕ} (hnk : n ≠ k) (x y : ℝ) :
    realDetector n (v n x + v k y) = x ∧
    realDetector k (v n x + v k y) = y := by
  constructor
  · refine (map_add (realDetector n) (v n x) (v k y)).trans ?_
    exact (congrArg₂ (fun a b : ℝ ↦ a + b)
      (realDetector_v n n x) (realDetector_v n k y)).trans
        (by simp only [ite_true, ite_eq_right hnk, add_zero])
  · refine (map_add (realDetector k) (v n x) (v k y)).trans ?_
    exact (congrArg₂ (fun a b : ℝ ↦ a + b)
      (realDetector_v k n x) (realDetector_v k k y)).trans
        (by simp only [ite_true, ite_eq_right hnk.symm, zero_add])

/-- A mixed tensor with both real coordinates nonzero has two nonzero evaluations. -/
theorem v_mixed_controls {n k : ℕ} (hnk : n ≠ k) {x y : ℝ}
    (hx : x ≠ 0) (hy : y ≠ 0) :
    realDetector n (v n x + v k y) ≠ 0 ∧
    realDetector k (v n x + v k y) ≠ 0 ∧ v n x + v k y ≠ 0 := by
  have hm := realDetector_mixed hnk x y
  refine ⟨hm.1.symm ▸ hx, hm.2.symm ▸ hy, ?_⟩
  intro h
  apply hx
  exact hm.1.symm.trans (by rw [h, map_zero])

/-- The complementary integer input at a Finsupp index. -/
noncomputable def w (n : ℕ) : finsuppTensor :=
  (Finsupp.single n 1 : finsuppCoefficients) ⊗ₜ[ℤ] ((1, 0) : rightModule)

/-- The two right coordinates give independent detector controls. -/
theorem finsuppTensor_right_controls (n : ℕ) (x : ℝ) :
    integerDetector n (w n) = 1 ∧ realDetector n (w n) = 0 ∧
    integerDetector n (v n x) = 0 ∧ realDetector n (v n x) = x := by
  refine ⟨(integerDetector_tmul n (Finsupp.single n 1) 1 0).trans ?_,
    (realDetector_tmul n (Finsupp.single n 1) 1 0).trans ?_,
    (integerDetector_tmul n (Finsupp.single n 1) 0 x).trans ?_,
    (realDetector_tmul n (Finsupp.single n 1) 0 x).trans ?_⟩ <;> simp

/-- The complementary integer tensor is nonzero at every index. -/
theorem w_ne_zero (n : ℕ) : w n ≠ 0 := by
  intro h
  have hi := (finsuppTensor_right_controls n 0).1
  rw [h, map_zero] at hi
  norm_num at hi

/-- The continuous coefficient inclusion of the torsion block. -/
noncomputable def includeC : torsionTensor →L[ℤ] productTensor :=
  TopModuleCat.tensorMapCLM ℤ (LinearMap.inl ℤ torsionCoefficients finsuppCoefficients)
    (ContinuousLinearMap.id ℤ rightModule)

/-- The continuous coefficient inclusion of the Finsupp block. -/
noncomputable def includeD : finsuppTensor →L[ℤ] productTensor :=
  TopModuleCat.tensorMapCLM ℤ (LinearMap.inr ℤ torsionCoefficients finsuppCoefficients)
    (ContinuousLinearMap.id ℤ rightModule)

/-- The continuous coefficient projection to the torsion block. -/
noncomputable def projectC : productTensor →L[ℤ] torsionTensor :=
  TopModuleCat.tensorMapCLM ℤ (LinearMap.fst ℤ torsionCoefficients finsuppCoefficients)
    (ContinuousLinearMap.id ℤ rightModule)

/-- The continuous coefficient projection to the Finsupp block. -/
noncomputable def projectD : productTensor →L[ℤ] finsuppTensor :=
  TopModuleCat.tensorMapCLM ℤ (LinearMap.snd ℤ torsionCoefficients finsuppCoefficients)
    (ContinuousLinearMap.id ℤ rightModule)

/-- Forgetting continuity gives the four stock tensor maps, on the whole carriers. -/
theorem primitive_maps_toLinearMap :
    includeC.toLinearMap = TensorProduct.map
      (LinearMap.inl ℤ torsionCoefficients finsuppCoefficients)
      (LinearMap.id : rightModule →ₗ[ℤ] rightModule) ∧
    includeD.toLinearMap = TensorProduct.map
      (LinearMap.inr ℤ torsionCoefficients finsuppCoefficients)
      (LinearMap.id : rightModule →ₗ[ℤ] rightModule) ∧
    projectC.toLinearMap = TensorProduct.map
      (LinearMap.fst ℤ torsionCoefficients finsuppCoefficients)
      (LinearMap.id : rightModule →ₗ[ℤ] rightModule) ∧
    projectD.toLinearMap = TensorProduct.map
      (LinearMap.snd ℤ torsionCoefficients finsuppCoefficients)
      (LinearMap.id : rightModule →ₗ[ℤ] rightModule) :=
  ⟨TopModuleCat.tensorMapCLM_toLinearMap ℤ _ _,
    TopModuleCat.tensorMapCLM_toLinearMap ℤ _ _,
    TopModuleCat.tensorMapCLM_toLinearMap ℤ _ _,
    TopModuleCat.tensorMapCLM_toLinearMap ℤ _ _⟩

/-- The four primitive maps act on all coefficient and right generator inputs. -/
theorem primitive_maps_tmul (c : torsionCoefficients) (d : finsuppCoefficients)
    (m : rightModule) :
    includeC (c ⊗ₜ[ℤ] m) = ((c, 0) : productCoefficients) ⊗ₜ[ℤ] m ∧
    includeD (d ⊗ₜ[ℤ] m) = ((0, d) : productCoefficients) ⊗ₜ[ℤ] m ∧
    projectC (((c, d) : productCoefficients) ⊗ₜ[ℤ] m) = c ⊗ₜ[ℤ] m ∧
    projectD (((c, d) : productCoefficients) ⊗ₜ[ℤ] m) = d ⊗ₜ[ℤ] m := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact TopModuleCat.tensorMapCLM_tmul ℤ
      (C := torsionCoefficients) (D := productCoefficients)
      (M := rightModule) (N := rightModule)
      (LinearMap.inl ℤ torsionCoefficients finsuppCoefficients)
      (ContinuousLinearMap.id ℤ rightModule) c m
  · exact TopModuleCat.tensorMapCLM_tmul ℤ
      (C := finsuppCoefficients) (D := productCoefficients)
      (M := rightModule) (N := rightModule)
      (LinearMap.inr ℤ torsionCoefficients finsuppCoefficients)
      (ContinuousLinearMap.id ℤ rightModule) d m
  · exact TopModuleCat.tensorMapCLM_tmul ℤ
      (C := productCoefficients) (D := torsionCoefficients)
      (M := rightModule) (N := rightModule)
      (LinearMap.fst ℤ torsionCoefficients finsuppCoefficients)
      (ContinuousLinearMap.id ℤ rightModule) ((c, d) : productCoefficients) m
  · exact TopModuleCat.tensorMapCLM_tmul ℤ
      (C := productCoefficients) (D := finsuppCoefficients)
      (M := rightModule) (N := rightModule)
      (LinearMap.snd ℤ torsionCoefficients finsuppCoefficients)
      (ContinuousLinearMap.id ℤ rightModule) ((c, d) : productCoefficients) m

/-- Each inclusion is split by its own projection. -/
theorem diagonal_composites :
    projectC.comp includeC = ContinuousLinearMap.id ℤ torsionTensor ∧
    projectD.comp includeD = ContinuousLinearMap.id ℤ finsuppTensor := by
  constructor
  · exact TopModuleCat.tensorMapCLM_comp_eq_id ℤ
      (C := torsionCoefficients) (D := productCoefficients)
      (M := rightModule) (N := rightModule)
      (LinearMap.inl ℤ torsionCoefficients finsuppCoefficients)
      (LinearMap.fst ℤ torsionCoefficients finsuppCoefficients)
      (ContinuousLinearMap.id ℤ rightModule) (ContinuousLinearMap.id ℤ rightModule)
      (LinearMap.fst_comp_inl ℤ torsionCoefficients finsuppCoefficients)
      (ContinuousLinearMap.id_comp (ContinuousLinearMap.id ℤ rightModule))
  · exact TopModuleCat.tensorMapCLM_comp_eq_id ℤ
      (C := finsuppCoefficients) (D := productCoefficients)
      (M := rightModule) (N := rightModule)
      (LinearMap.inr ℤ torsionCoefficients finsuppCoefficients)
      (LinearMap.snd ℤ torsionCoefficients finsuppCoefficients)
      (ContinuousLinearMap.id ℤ rightModule) (ContinuousLinearMap.id ℤ rightModule)
      (LinearMap.snd_comp_inr ℤ torsionCoefficients finsuppCoefficients)
      (ContinuousLinearMap.id_comp (ContinuousLinearMap.id ℤ rightModule))

/-- Each inclusion is killed by the other projection. -/
theorem off_diagonal_composites : projectC.comp includeD = 0 ∧ projectD.comp includeC = 0 := by
  constructor
  · apply TopModuleCat.tensorLeft_ext ℤ
      (C := finsuppCoefficients) (M := rightModule) (N := torsionTensor)
    intro d m
    have hg := primitive_maps_tmul (0 : torsionCoefficients) d m
    have hi : projectC (includeD (d ⊗ₜ[ℤ] m : finsuppTensor)) = (0 : torsionTensor) :=
      (congrArg projectC hg.2.1).trans
        (hg.2.2.1.trans (TensorProduct.zero_tmul torsionCoefficients m))
    have hz : (0 : finsuppTensor →L[ℤ] torsionTensor)
        (d ⊗ₜ[ℤ] m : finsuppTensor) = (0 : torsionTensor) := zero_apply _
    exact (ContinuousLinearMap.comp_apply projectC includeD
      (d ⊗ₜ[ℤ] m : finsuppTensor)).trans (hi.trans hz.symm)
  · apply TopModuleCat.tensorLeft_ext ℤ
      (C := torsionCoefficients) (M := rightModule) (N := finsuppTensor)
    intro c m
    have hg := primitive_maps_tmul c (0 : finsuppCoefficients) m
    have hi : projectD (includeC (c ⊗ₜ[ℤ] m : torsionTensor)) = (0 : finsuppTensor) :=
      (congrArg projectD hg.1).trans
        (hg.2.2.2.trans (TensorProduct.zero_tmul finsuppCoefficients m))
    have hz : (0 : torsionTensor →L[ℤ] finsuppTensor)
        (c ⊗ₜ[ℤ] m : torsionTensor) = (0 : finsuppTensor) := zero_apply _
    exact (ContinuousLinearMap.comp_apply projectD includeC
      (c ⊗ₜ[ℤ] m : torsionTensor)).trans (hi.trans hz.symm)

/-- Projection formulas hold for every pair of block tensors. -/
theorem projection_inclusion_values (s : torsionTensor) (t : finsuppTensor) :
    projectC (includeC s) = s ∧ projectD (includeD t) = t ∧
    projectC (includeD t) = 0 ∧ projectD (includeC s) = 0 := by
  exact ⟨DFunLike.congr_fun diagonal_composites.1 s,
    DFunLike.congr_fun diagonal_composites.2 t,
    DFunLike.congr_fun off_diagonal_composites.1 t,
    DFunLike.congr_fun off_diagonal_composites.2 s⟩

/-- The mixed inclusion has the specified projections for arbitrary inputs. -/
theorem mixed_projections (s : torsionTensor) (t : finsuppTensor) :
    projectC (includeC s + includeD t) = s ∧
    projectD (includeC s + includeD t) = t := by
  have h := projection_inclusion_values s t
  constructor <;> simp only [map_add, h.1, h.2.1, h.2.2.1, h.2.2.2, add_zero, zero_add]

/-- The two coefficient projections reconstruct every tensor by their inclusions. -/
theorem reconstruct (z : productTensor) :
    includeC (projectC z) + includeD (projectD z) = z := by
  have h : includeC.comp projectC + includeD.comp projectD =
      ContinuousLinearMap.id ℤ productTensor := by
    apply TopModuleCat.tensorLeft_ext ℤ
      (C := productCoefficients) (M := rightModule) (N := productTensor)
    intro p m
    rcases p with ⟨c, d⟩
    let t : productTensor := ((c, d) : productCoefficients) ⊗ₜ[ℤ] m
    have hp : ((c, 0) : productCoefficients) + ((0, d) : productCoefficients) =
        ((c, d) : productCoefficients) :=
      Prod.ext (add_zero c) (zero_add d)
    have hg := primitive_maps_tmul c d m
    have hc : includeC (projectC t) = ((c, 0) : productCoefficients) ⊗ₜ[ℤ] m :=
      (congrArg includeC hg.2.2.1).trans hg.1
    have hd : includeD (projectD t) = ((0, d) : productCoefficients) ⊗ₜ[ℤ] m :=
      (congrArg includeD hg.2.2.2).trans hg.2.1
    have ha : (includeC.comp projectC + includeD.comp projectD) t =
        includeC (projectC t) + includeD (projectD t) :=
      (add_apply (includeC.comp projectC) (includeD.comp projectD) t).trans
        (congrArg₂ (fun s t : productTensor ↦ s + t)
          (ContinuousLinearMap.comp_apply includeC projectC t)
          (ContinuousLinearMap.comp_apply includeD projectD t))
    have hr : includeC (projectC t) + includeD (projectD t) = t :=
      (congrArg₂ (fun s t : productTensor ↦ s + t) hc hd).trans
        ((TensorProduct.add_tmul ((c, 0) : productCoefficients)
          ((0, d) : productCoefficients) m).symm.trans
            (congrArg (fun q : productCoefficients ↦ (q ⊗ₜ[ℤ] m : productTensor)) hp))
    have hi : ContinuousLinearMap.id ℤ productTensor t = t :=
      ContinuousLinearMap.id_apply t
    exact ha.trans (hr.trans hi.symm)
  have ha : (includeC.comp projectC + includeD.comp projectD) z =
      includeC (projectC z) + includeD (projectD z) :=
    (add_apply (includeC.comp projectC) (includeD.comp projectD) z).trans
      (congrArg₂ (fun s t : productTensor ↦ s + t)
        (ContinuousLinearMap.comp_apply includeC projectC z)
        (ContinuousLinearMap.comp_apply includeD projectD z))
  have hi : ContinuousLinearMap.id ℤ productTensor z = z :=
    ContinuousLinearMap.id_apply z
  exact ha.symm.trans ((DFunLike.congr_fun h z).trans hi)

/-- Supported images of both independent torsion tensors and every real direction survive. -/
theorem included_controls (n : ℕ) {x : ℝ} (hx : x ≠ 0) :
    includeC u0 ≠ 0 ∧ includeC u1 ≠ 0 ∧ includeC u0 ≠ includeC u1 ∧
    includeD (v n x) ≠ 0 ∧ includeC u0 ≠ includeD (v n x) := by
  have h0 := projection_inclusion_values u0 (v n x)
  have h1 := projection_inclusion_values u1 (v n x)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h
    exact torsionTensor_controls.1 (h0.1.symm.trans (by rw [h, map_zero]))
  · intro h
    exact torsionTensor_controls.2.1 (h1.1.symm.trans (by rw [h, map_zero]))
  · intro h
    apply torsionTensor_controls.2.2.1
    exact h0.1.symm.trans ((congrArg projectC h).trans h1.1)
  · intro h
    exact v_ne_zero n hx (h0.2.1.symm.trans (by rw [h, map_zero]))
  · intro h
    exact torsionTensor_controls.1 (h0.1.symm.trans ((congrArg projectC h).trans h0.2.2.1))

/-- A mixed product tensor has two nonzero projections and reconstructs from them. -/
theorem productTensor_mixed_controls (n : ℕ) {x : ℝ} (hx : x ≠ 0) :
    projectC (includeC u0 + includeD (v n x)) ≠ 0 ∧
    projectD (includeC u0 + includeD (v n x)) ≠ 0 ∧
    includeC u0 + includeD (v n x) ≠ 0 ∧
    includeC (projectC (includeC u0 + includeD (v n x))) +
      includeD (projectD (includeC u0 + includeD (v n x))) =
        includeC u0 + includeD (v n x) := by
  have hm := mixed_projections u0 (v n x)
  refine ⟨hm.1.symm ▸ torsionTensor_controls.1, hm.2.symm ▸ v_ne_zero n hx, ?_,
    reconstruct _⟩
  intro h
  exact torsionTensor_controls.1 (hm.1.symm.trans (by rw [h, map_zero]))

/-- A mixed tensor differs from either of its supported components. -/
theorem productTensor_mixed_distinct (n : ℕ) {x : ℝ} (hx : x ≠ 0) :
    includeC u0 + includeD (v n x) ≠ includeC u0 ∧
    includeC u0 + includeD (v n x) ≠ includeD (v n x) := by
  have hm := mixed_projections u0 (v n x)
  have hi := projection_inclusion_values u0 (v n x)
  constructor
  · intro h
    exact v_ne_zero n hx (hm.2.symm.trans ((congrArg projectD h).trans hi.2.2.2))
  · intro h
    exact torsionTensor_controls.1 (hm.1.symm.trans ((congrArg projectC h).trans hi.2.2.1))

/-- Mathlib's algebraic tensor equivalence distributing over the product of the
two coefficient modules. -/
noncomputable def algebraicProductEquiv : productTensor ≃ₗ[ℤ] tensorOutput :=
  TensorProduct.prodLeft ℤ ℤ torsionCoefficients finsuppCoefficients rightModule

/-- The stock algebraic equivalence agrees with both primitive maps on all inputs. -/
theorem algebraicProductEquiv_apply (z : productTensor) :
    algebraicProductEquiv z = (projectC z, projectD z) := by
  have h : algebraicProductEquiv.toLinearMap = projectC.toLinearMap.prod projectD.toLinearMap := by
    apply TensorProduct.ext'
    intro p m
    rcases p with ⟨c, d⟩
    let t : productTensor := ((c, d) : productCoefficients) ⊗ₜ[ℤ] m
    have he : algebraicProductEquiv.toLinearMap t =
        (((c ⊗ₜ[ℤ] m : torsionTensor), (d ⊗ₜ[ℤ] m : finsuppTensor)) : tensorOutput) :=
      TensorProduct.prodLeft_tmul ℤ ℤ torsionCoefficients finsuppCoefficients rightModule c d m
    have hg := primitive_maps_tmul c d m
    have hp : projectC.toLinearMap.prod projectD.toLinearMap t =
        (((c ⊗ₜ[ℤ] m : torsionTensor), (d ⊗ₜ[ℤ] m : finsuppTensor)) : tensorOutput) :=
      (LinearMap.prod_apply projectC.toLinearMap projectD.toLinearMap t).trans
        (Prod.ext hg.2.2.1 hg.2.2.2)
    exact he.trans hp.symm
  exact DFunLike.congr_fun h z

/-- The stock inverse reconstructs an arbitrary pair, not only pairs of pure tensors. -/
theorem algebraicProductEquiv_symm_apply (s : torsionTensor) (t : finsuppTensor) :
    algebraicProductEquiv.symm (s, t) = includeC s + includeD t := by
  apply algebraicProductEquiv.injective
  rw [algebraicProductEquiv.apply_symm_apply, algebraicProductEquiv_apply]
  exact (Prod.ext (mixed_projections s t).1 (mixed_projections s t).2).symm

/-- The mixed specimen has the two specified components under the stock equivalence. -/
theorem algebraicProductEquiv_mixed (n : ℕ) (x : ℝ) :
    algebraicProductEquiv (includeC u0 + includeD (v n x)) = (u0, v n x) := by
  rw [algebraicProductEquiv_apply]
  exact Prod.ext (mixed_projections u0 (v n x)).1 (mixed_projections u0 (v n x)).2


/-- Coefficient-product distribution and its inverse agree with the specimen's block maps
on all inputs. -/
theorem tensorProdLeft_values
    (z : productTensor) (s : torsionTensor) (t : finsuppTensor) :
  TopModuleCat.tensorProdLeft ℤ torsionCoefficients finsuppCoefficients rightModule z =
    (projectC z, projectD z) ∧
  (TopModuleCat.tensorProdLeft ℤ torsionCoefficients finsuppCoefficients rightModule).symm
    (s,t) = includeC s + includeD t := by
  exact ⟨DFunLike.congr_fun
    (TopModuleCat.tensorProdLeft_toContinuousLinearMap ℤ
      torsionCoefficients finsuppCoefficients rightModule) z,
    TopModuleCat.tensorProdLeft_symm_apply_pair ℤ
      torsionCoefficients finsuppCoefficients rightModule s t⟩

/-- The whole continuous distribution maps are the specimen's projection product and
inclusion sum. -/
theorem tensorProdLeft_maps :
  (TopModuleCat.tensorProdLeft ℤ torsionCoefficients finsuppCoefficients
    rightModule).toContinuousLinearMap = projectC.prod projectD ∧
  (TopModuleCat.tensorProdLeft ℤ torsionCoefficients finsuppCoefficients
    rightModule).symm.toContinuousLinearMap =
      includeC.comp (ContinuousLinearMap.fst ℤ torsionTensor finsuppTensor) +
      includeD.comp (ContinuousLinearMap.snd ℤ torsionTensor finsuppTensor) := by
  exact ⟨TopModuleCat.tensorProdLeft_toContinuousLinearMap ℤ
    torsionCoefficients finsuppCoefficients rightModule,
    TopModuleCat.tensorProdLeft_symm_toContinuousLinearMap ℤ
      torsionCoefficients finsuppCoefficients rightModule⟩

/-- All three algebraic detectors evaluate distributed pure tensors at every coefficient
and right input. -/
theorem tensorProdLeft_detector_tmul
    (c : torsionCoefficients) (d : finsuppCoefficients) (a : ℤ) (x : ℝ) (i : ℕ) :
  torsionDetector
    (TopModuleCat.tensorProdLeft ℤ torsionCoefficients finsuppCoefficients rightModule
      (((c,d) : productCoefficients) ⊗ₜ[ℤ] ((a,x) : rightModule))).1 = a • c ∧
  realDetector i
    (TopModuleCat.tensorProdLeft ℤ torsionCoefficients finsuppCoefficients rightModule
      (((c,d) : productCoefficients) ⊗ₜ[ℤ] ((a,x) : rightModule))).2 = (d i : ℝ) * x ∧
  integerDetector i
    (TopModuleCat.tensorProdLeft ℤ torsionCoefficients finsuppCoefficients rightModule
      (((c,d) : productCoefficients) ⊗ₜ[ℤ] ((a,x) : rightModule))).2 = d i * a := by
  rw [TopModuleCat.tensorProdLeft_tmul]
  exact ⟨torsionDetector_tmul c a x, realDetector_tmul i d a x,
    integerDetector_tmul i d a x⟩

/-- A mixed distributed tensor retains both torsion directions, an integer component
and two nonzero real evaluations. -/
theorem tensorProdLeft_mixed_controls
    {n k : ℕ} (hnk : n ≠ k) {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) :
  TopModuleCat.tensorProdLeft ℤ torsionCoefficients finsuppCoefficients rightModule
    (includeC (u0+u1) + includeD (w n + v n x + v k y)) =
      (u0+u1, w n + v n x + v k y) ∧
  (TopModuleCat.tensorProdLeft ℤ torsionCoefficients finsuppCoefficients rightModule
    (includeC (u0+u1) + includeD (w n + v n x + v k y))).1 ≠ 0 ∧
  (TopModuleCat.tensorProdLeft ℤ torsionCoefficients finsuppCoefficients rightModule
    (includeC (u0+u1) + includeD (w n + v n x + v k y))).2 ≠ 0 ∧
  torsionDetector
    (TopModuleCat.tensorProdLeft ℤ torsionCoefficients finsuppCoefficients rightModule
      (includeC (u0+u1) + includeD (w n + v n x + v k y))).1 = c0+c1 ∧
  integerDetector n
    (TopModuleCat.tensorProdLeft ℤ torsionCoefficients finsuppCoefficients rightModule
      (includeC (u0+u1) + includeD (w n + v n x + v k y))).2 = 1 ∧
  realDetector n
    (TopModuleCat.tensorProdLeft ℤ torsionCoefficients finsuppCoefficients rightModule
      (includeC (u0+u1) + includeD (w n + v n x + v k y))).2 = x ∧
  realDetector k
    (TopModuleCat.tensorProdLeft ℤ torsionCoefficients finsuppCoefficients rightModule
      (includeC (u0+u1) + includeD (w n + v n x + v k y))).2 = y ∧
  realDetector n
    (TopModuleCat.tensorProdLeft ℤ torsionCoefficients finsuppCoefficients rightModule
      (includeC (u0+u1) + includeD (w n + v n x + v k y))).2 ≠ 0 ∧
  realDetector k
    (TopModuleCat.tensorProdLeft ℤ torsionCoefficients finsuppCoefficients rightModule
      (includeC (u0+u1) + includeD (w n + v n x + v k y))).2 ≠ 0 ∧
  includeC (u0+u1) + includeD (w n + v n x + v k y) ≠ 0 ∧
  (TopModuleCat.tensorProdLeft ℤ torsionCoefficients finsuppCoefficients rightModule).symm
    (u0+u1, w n + v n x + v k y) =
      includeC (u0+u1) + includeD (w n + v n x + v k y) := by
  let t : finsuppTensor := w n + v n x + v k y
  have he : TopModuleCat.tensorProdLeft ℤ torsionCoefficients finsuppCoefficients
      rightModule (includeC (u0 + u1) + includeD t) = (u0 + u1, t) :=
    (tensorProdLeft_values _ (u0 + u1) t).1.trans
      (Prod.ext (mixed_projections (u0 + u1) t).1 (mixed_projections (u0 + u1) t).2)
  have ht : torsionDetector (u0 + u1) = c0 + c1 :=
    (map_add torsionDetector u0 u1).trans
      (congrArg₂ (fun a b : torsionCoefficients ↦ a + b)
        ((torsionDetector_tmul c0 1 0).trans (one_smul ℤ c0))
        ((torsionDetector_tmul c1 1 0).trans (one_smul ℤ c1)))
  have hiv : integerDetector n (v n x + v k y) = 0 :=
    (map_add (integerDetector n) (v n x) (v k y)).trans
      ((congrArg₂ (fun a b : ℤ ↦ a + b)
        (finsuppTensor_right_controls n x).2.2.1
        ((integerDetector_tmul n (Finsupp.single k 1) 0 y).trans (mul_zero _))).trans
          (zero_add (0 : ℤ)))
  have hi : integerDetector n t = 1 :=
    (congrArg (integerDetector n) (add_assoc (w n) (v n x) (v k y))).trans
      ((map_add (integerDetector n) (w n) (v n x + v k y)).trans
        ((congrArg₂ (fun a b : ℤ ↦ a + b)
          (finsuppTensor_right_controls n x).1 hiv).trans (add_zero 1)))
  have hm := realDetector_mixed hnk x y
  have hwk : realDetector k (w n) = 0 :=
    (realDetector_tmul k (Finsupp.single n 1) 1 0).trans (mul_zero _)
  have hr : realDetector n t = x ∧ realDetector k t = y := by
    constructor
    · exact (congrArg (realDetector n) (add_assoc (w n) (v n x) (v k y))).trans
        ((map_add (realDetector n) (w n) (v n x + v k y)).trans
          ((congrArg₂ (fun a b : ℝ ↦ a + b)
            (finsuppTensor_right_controls n x).2.1 hm.1).trans (zero_add x)))
    · exact (congrArg (realDetector k) (add_assoc (w n) (v n x) (v k y))).trans
        ((map_add (realDetector k) (w n) (v n x + v k y)).trans
          ((congrArg₂ (fun a b : ℝ ↦ a + b) hwk hm.2).trans (zero_add y)))
  have ht0 : t ≠ 0 := by
    intro hz
    exact hx (hr.1.symm.trans
      ((congrArg (realDetector n) hz).trans (map_zero (realDetector n))))
  have hfst := congrArg Prod.fst he
  have hsnd := congrArg Prod.snd he
  have hdn := (congrArg (realDetector n) hsnd).trans hr.1
  have hdk := (congrArg (realDetector k) hsnd).trans hr.2
  refine ⟨he, ?_, ?_, (congrArg torsionDetector hfst).trans ht,
    (congrArg (integerDetector n) hsnd).trans hi, hdn, hdk,
    (fun hz ↦ hx (hdn.symm.trans hz)), (fun hz ↦ hy (hdk.symm.trans hz)), ?_,
    (tensorProdLeft_values (includeC (u0 + u1) + includeD t) (u0 + u1) t).2⟩
  · intro hz
    exact torsionTensor_controls.2.2.2 (hfst.symm.trans hz)
  · intro hz
    exact ht0 (hsnd.symm.trans hz)
  · intro hz
    have hp := congrArg Prod.fst he
    rw [hz, map_zero] at hp
    exact torsionTensor_controls.2.2.2 hp.symm

/-- Forward and inverse distribution commute with independent coefficient and right-module maps. -/
theorem tensorProdLeft_naturality
    (f : torsionCoefficients →ₗ[ℤ] torsionCoefficients)
    (g : finsuppCoefficients →ₗ[ℤ] finsuppCoefficients)
    (h : rightModule →L[ℤ] rightModule) :
  ((TopModuleCat.tensorMapCLM ℤ (C := torsionCoefficients) (D := torsionCoefficients)
    (M := rightModule) (N := rightModule) f h).prodMap
    (TopModuleCat.tensorMapCLM ℤ (C := finsuppCoefficients) (D := finsuppCoefficients)
      (M := rightModule) (N := rightModule) g h)).comp
    (TopModuleCat.tensorProdLeft ℤ torsionCoefficients finsuppCoefficients
      rightModule).toContinuousLinearMap =
  (TopModuleCat.tensorProdLeft ℤ torsionCoefficients finsuppCoefficients
    rightModule).toContinuousLinearMap.comp
    (TopModuleCat.tensorMapCLM ℤ (C := productCoefficients) (D := productCoefficients)
      (M := rightModule) (N := rightModule) (f.prodMap g) h) ∧
  (TopModuleCat.tensorMapCLM ℤ (C := productCoefficients) (D := productCoefficients)
    (M := rightModule) (N := rightModule) (f.prodMap g) h).comp
    (TopModuleCat.tensorProdLeft ℤ torsionCoefficients finsuppCoefficients
      rightModule).symm.toContinuousLinearMap =
  (TopModuleCat.tensorProdLeft ℤ torsionCoefficients finsuppCoefficients
    rightModule).symm.toContinuousLinearMap.comp
    ((TopModuleCat.tensorMapCLM ℤ (C := torsionCoefficients) (D := torsionCoefficients)
      (M := rightModule) (N := rightModule) f h).prodMap
      (TopModuleCat.tensorMapCLM ℤ (C := finsuppCoefficients) (D := finsuppCoefficients)
        (M := rightModule) (N := rightModule) g h)) := by
  exact ⟨TopModuleCat.tensorProdLeft_naturality ℤ f g h,
    TopModuleCat.tensorProdLeft_symm_naturality ℤ f g h⟩

/-- Independent coefficient and right-module maps distribute the full mixed tensor componentwise. -/
theorem tensorProdLeft_mapped_mixed
    (f : torsionCoefficients →ₗ[ℤ] torsionCoefficients)
    (g : finsuppCoefficients →ₗ[ℤ] finsuppCoefficients)
    (h : rightModule →L[ℤ] rightModule) (n k : ℕ) (x y : ℝ) :
  TopModuleCat.tensorProdLeft ℤ torsionCoefficients finsuppCoefficients rightModule
    (TopModuleCat.tensorMapCLM ℤ (C := productCoefficients) (D := productCoefficients)
      (M := rightModule) (N := rightModule) (f.prodMap g) h
      (includeC (u0+u1) + includeD (w n + v n x + v k y))) =
  (TopModuleCat.tensorMapCLM ℤ (C := torsionCoefficients) (D := torsionCoefficients)
      (M := rightModule) (N := rightModule) f h (u0+u1),
    TopModuleCat.tensorMapCLM ℤ (C := finsuppCoefficients) (D := finsuppCoefficients)
      (M := rightModule) (N := rightModule) g h (w n + v n x + v k y)) := by
  have he : TopModuleCat.tensorProdLeft ℤ torsionCoefficients finsuppCoefficients
      rightModule (includeC (u0 + u1) + includeD (w n + v n x + v k y)) =
        (u0 + u1, w n + v n x + v k y) :=
    (tensorProdLeft_values _ (u0 + u1) (w n + v n x + v k y)).1.trans
      (Prod.ext (mixed_projections (u0 + u1) (w n + v n x + v k y)).1
        (mixed_projections (u0 + u1) (w n + v n x + v k y)).2)
  have hn := DFunLike.congr_fun (tensorProdLeft_naturality f g h).1
    (includeC (u0 + u1) + includeD (w n + v n x + v k y))
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    he, ContinuousLinearMap.coe_prodMap', Prod.map_apply] using hn.symm

/-- Doubling the Finsupp coefficients preserves the mixed torsion component
and changes the detected image. -/
theorem tensorProdLeft_scaled_mixed
    (n k : ℕ) (hnk : n ≠ k) :
  TopModuleCat.tensorProdLeft ℤ torsionCoefficients finsuppCoefficients rightModule
    (TopModuleCat.tensorMapCLM ℤ (C := productCoefficients) (D := productCoefficients)
      (M := rightModule) (N := rightModule)
      ((LinearMap.id : torsionCoefficients →ₗ[ℤ] torsionCoefficients).prodMap
        ((2 : ℤ) • (LinearMap.id : finsuppCoefficients →ₗ[ℤ] finsuppCoefficients)))
      (ContinuousLinearMap.id ℤ rightModule)
      (includeC (u0+u1) + includeD (w n + v n 1 + v k 2))) =
    (u0+u1, (2 : ℤ) • (w n + v n 1 + v k 2)) ∧
  torsionDetector (u0+u1) = c0+c1 ∧
  integerDetector n ((2 : ℤ) • (w n + v n 1 + v k 2)) = 2 ∧
  realDetector n ((2 : ℤ) • (w n + v n 1 + v k 2)) = 2 ∧
  realDetector k ((2 : ℤ) • (w n + v n 1 + v k 2)) = 4 ∧
  TopModuleCat.tensorProdLeft ℤ torsionCoefficients finsuppCoefficients rightModule
    (TopModuleCat.tensorMapCLM ℤ (C := productCoefficients) (D := productCoefficients)
      (M := rightModule) (N := rightModule)
      ((LinearMap.id : torsionCoefficients →ₗ[ℤ] torsionCoefficients).prodMap
        ((2 : ℤ) • (LinearMap.id : finsuppCoefficients →ₗ[ℤ] finsuppCoefficients)))
      (ContinuousLinearMap.id ℤ rightModule)
      (includeC (u0+u1) + includeD (w n + v n 1 + v k 2))) ≠
    (u0+u1, w n + v n 1 + v k 2) := by
  let t : finsuppTensor := w n + v n 1 + v k 2
  have hs := tensorProdLeft_mapped_mixed
    (LinearMap.id : torsionCoefficients →ₗ[ℤ] torsionCoefficients)
    ((2 : ℤ) • (LinearMap.id : finsuppCoefficients →ₗ[ℤ] finsuppCoefficients))
    (ContinuousLinearMap.id ℤ rightModule) n k 1 2
  have hc := tensorProdLeft_mixed_controls hnk
    (by norm_num : (1 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)
  have ht : torsionDetector (u0 + u1) = c0 + c1 := by
    simpa only [hc.1] using hc.2.2.2.1
  have hi : integerDetector n t = 1 := by
    simpa only [hc.1] using hc.2.2.2.2.1
  have hn : realDetector n t = 1 := by
    simpa only [hc.1] using hc.2.2.2.2.2.1
  have hk : realDetector k t = 2 := by
    simpa only [hc.1] using hc.2.2.2.2.2.2.1
  have hi2 : integerDetector n ((2 : ℤ) • t) = 2 := by
    rw [map_smul, hi]
    norm_num
  have hn2 : realDetector n ((2 : ℤ) • t) = 2 := by
    rw [map_smul, hn]
    norm_num
  have hk2 : realDetector k ((2 : ℤ) • t) = 4 := by
    rw [map_smul, hk]
    norm_num
  refine ⟨hs, ht, hi2, hn2, hk2, ?_⟩
  intro heq
  have hd := congrArg (fun p : tensorOutput ↦ realDetector n p.2) heq
  rw [hs] at hd
  change realDetector n ((2 : ℤ) • t) = realDetector n t at hd
  rw [hn2, hn] at hd
  norm_num at hd

end CoefficientTensorProdExamples
