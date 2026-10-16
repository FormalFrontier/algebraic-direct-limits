/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicDirectLimitsExamples.CoefficientTensorProd
public import AlgebraicDirectLimits.Topology.TensorProduct.Quotient
public import AlgebraicDirectLimits.Topology.TensorCircle.Detector
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.Algebra.Module.Submodule.RestrictScalars
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
public import Mathlib.Topology.Algebra.Order.Archimedean

/-!
# Quotients of torsion and infinitely generated coefficient tensors

The right module is `ℤ × ℝ`, and the coefficient module is
`(ZMod 2 × ZMod 2) × (ℕ →₀ ℤ)`. For an integer submodule `B` of `ℝ`, the right
submodule is `2ℤ × B`. The two principal choices are `B = ⊥` and the rational
span of `1`, restricted to integer scalars. The latter submodule is not closed.
No topology on the coefficient module or detector targets is required.

`quotientTensor_boundaries` compares the generic zero and whole right submodules.
`quotientTensor_block_values` describes all four block maps, their off-diagonal
zeros, reconstruction and both equivalence recoveries. The algebraic descents
in `quotientTensor_detector_values` evaluate every coefficient and index.
`quotientTensor_mixed_controls` retains both torsion directions, an integer
coordinate modulo two and two independently supplied nonzero real classes at
distinct indices. It also includes nonzero tensors killed by the quotient.
`quotientTensor_mapped_values` allows independent coefficient maps and a
continuous right-module map preserving the submodule. In
`quotientTensor_scaled_values`, doubling the Finsupp coefficients kills the
modulo-two coordinate and changes both real coordinates.
`quotientTensor_nonclosed` concerns the rational submodule and the nonzero
classes of `√2`, `2√2` and `4√2`. The first two numbers are rationally dependent;
the independent controls are their distinct Finsupp indices, not these numbers.

## Implementation notes

The four continuous block maps are conjugated by `TopModuleCat.tensorQuotient`.
The detector descents are algebraic and do not use these conjugated maps.
The rational-class comparison uses
`Submodule.Quotient.restrictScalarsEquiv`, not a continuous identification with
an algebraic rational quotient. Rational cast density supplies the nonclosedness
argument. All module, quotient and joint-action structures are the canonical ones.

## References

The tensor-quotient equivalence is Mathlib's construction by Antoine
Chambert-Loir and Jujian Zhang; right exactness is due to Antoine Chambert-Loir.
Continuous quotient maps and descents follow Anatole Dedecker and Sharvil
Kesarwani. The coefficient blocks and controls follow the companion
`CoefficientTensorProd` module, using Eric Wieser's product equivalence, Kenny
Lau and Mario Carneiro's tensor maps and unitors, and Johannes Hölzl and Kim
Morrison's Finsupp API. Submodules, spans, integer actions and quotients use
Mathlib's work of Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro,
Kevin Buzzard, Yury Kudryashov, Frédéric Dupuis, Heather Macbeth and Andrew Yang;
ZMod is due to Chris Hughes. Rational cast density is due to Yury Kudryashov.
The rational-class detector follows the algebraic circle detector and
irrational-square-root argument in `TensorCircle.Detector`, with its cited
contributors. The topological-module lineage includes the
Continuous Group Cohomology development and Richard Hill and Andrew Yang's
Mathlib constructions. These examples were developed by Formal Frontier Agents
with AI assistance.
-/

-- These quotient tensor checks are private examples, not a downstream API.
set_option linter.privateModule false

noncomputable section

open scoped TensorProduct

namespace CoefficientTensorProdExamples

/-- Integer-real pairs whose integer coordinate is even and real coordinate lies in `B`. -/
private def evenRightSubmodule (B : Submodule ℤ ℝ) : Submodule ℤ rightModule :=
  (Submodule.span ℤ {(2 : ℤ)}).prod B

/-- Inclusion of the torsion block after quotienting the right factor. -/
private def quotientIncludeC (B : Submodule ℤ ℝ) :
    let P := evenRightSubmodule B
    let φ : (H : ModuleCat ℤ) →
        TopModuleCat.Hom
          (TopModuleCat.tensorLeftObj ℤ H (TopModuleCat.of ℤ P))
          (TopModuleCat.tensorLeftObj ℤ H rightModule) :=
      fun H ↦ CategoryTheory.ConcreteCategory.ofHom
        (C := TopModuleCat ℤ)
        (X := TopModuleCat.tensorLeftObj ℤ H (TopModuleCat.of ℤ P))
        (Y := TopModuleCat.tensorLeftObj ℤ H rightModule)
        (TopModuleCat.tensorMapCLM ℤ (C := H) (D := H)
          (M := TopModuleCat.of ℤ P) (N := rightModule)
          (LinearMap.id : H →ₗ[ℤ] H) P.subtypeL)
    let Q := fun H : ModuleCat ℤ ↦ TopModuleCat.coker (φ H)
    Q torsionCoefficients →L[ℤ] Q productCoefficients :=
  (TopModuleCat.tensorQuotient ℤ productCoefficients rightModule
    (evenRightSubmodule B)).toContinuousLinearMap.comp
      ((TopModuleCat.tensorMapCLM ℤ
        (C := torsionCoefficients) (D := productCoefficients)
        (M := TopModuleCat.of ℤ (rightModule ⧸ evenRightSubmodule B))
        (N := TopModuleCat.of ℤ (rightModule ⧸ evenRightSubmodule B))
        (LinearMap.inl ℤ torsionCoefficients finsuppCoefficients)
        (ContinuousLinearMap.id ℤ (TopModuleCat.of ℤ
          (rightModule ⧸ evenRightSubmodule B)))).comp
        (TopModuleCat.tensorQuotient ℤ torsionCoefficients rightModule
          (evenRightSubmodule B)).symm.toContinuousLinearMap)

/-- Inclusion of the Finsupp block after quotienting the right factor. -/
private def quotientIncludeD (B : Submodule ℤ ℝ) :
    let P := evenRightSubmodule B
    let φ : (H : ModuleCat ℤ) →
        TopModuleCat.Hom
          (TopModuleCat.tensorLeftObj ℤ H (TopModuleCat.of ℤ P))
          (TopModuleCat.tensorLeftObj ℤ H rightModule) :=
      fun H ↦ CategoryTheory.ConcreteCategory.ofHom
        (C := TopModuleCat ℤ)
        (X := TopModuleCat.tensorLeftObj ℤ H (TopModuleCat.of ℤ P))
        (Y := TopModuleCat.tensorLeftObj ℤ H rightModule)
        (TopModuleCat.tensorMapCLM ℤ (C := H) (D := H)
          (M := TopModuleCat.of ℤ P) (N := rightModule)
          (LinearMap.id : H →ₗ[ℤ] H) P.subtypeL)
    let Q := fun H : ModuleCat ℤ ↦ TopModuleCat.coker (φ H)
    Q finsuppCoefficients →L[ℤ] Q productCoefficients :=
  (TopModuleCat.tensorQuotient ℤ productCoefficients rightModule
    (evenRightSubmodule B)).toContinuousLinearMap.comp
      ((TopModuleCat.tensorMapCLM ℤ
        (C := finsuppCoefficients) (D := productCoefficients)
        (M := TopModuleCat.of ℤ (rightModule ⧸ evenRightSubmodule B))
        (N := TopModuleCat.of ℤ (rightModule ⧸ evenRightSubmodule B))
        (LinearMap.inr ℤ torsionCoefficients finsuppCoefficients)
        (ContinuousLinearMap.id ℤ (TopModuleCat.of ℤ
          (rightModule ⧸ evenRightSubmodule B)))).comp
        (TopModuleCat.tensorQuotient ℤ finsuppCoefficients rightModule
          (evenRightSubmodule B)).symm.toContinuousLinearMap)

/-- Projection to the torsion block after quotienting the right factor. -/
private def quotientProjectC (B : Submodule ℤ ℝ) :
    let P := evenRightSubmodule B
    let φ : (H : ModuleCat ℤ) →
        TopModuleCat.Hom
          (TopModuleCat.tensorLeftObj ℤ H (TopModuleCat.of ℤ P))
          (TopModuleCat.tensorLeftObj ℤ H rightModule) :=
      fun H ↦ CategoryTheory.ConcreteCategory.ofHom
        (C := TopModuleCat ℤ)
        (X := TopModuleCat.tensorLeftObj ℤ H (TopModuleCat.of ℤ P))
        (Y := TopModuleCat.tensorLeftObj ℤ H rightModule)
        (TopModuleCat.tensorMapCLM ℤ (C := H) (D := H)
          (M := TopModuleCat.of ℤ P) (N := rightModule)
          (LinearMap.id : H →ₗ[ℤ] H) P.subtypeL)
    let Q := fun H : ModuleCat ℤ ↦ TopModuleCat.coker (φ H)
    Q productCoefficients →L[ℤ] Q torsionCoefficients :=
  (TopModuleCat.tensorQuotient ℤ torsionCoefficients rightModule
    (evenRightSubmodule B)).toContinuousLinearMap.comp
      ((TopModuleCat.tensorMapCLM ℤ
        (C := productCoefficients) (D := torsionCoefficients)
        (M := TopModuleCat.of ℤ (rightModule ⧸ evenRightSubmodule B))
        (N := TopModuleCat.of ℤ (rightModule ⧸ evenRightSubmodule B))
        (LinearMap.fst ℤ torsionCoefficients finsuppCoefficients)
        (ContinuousLinearMap.id ℤ (TopModuleCat.of ℤ
          (rightModule ⧸ evenRightSubmodule B)))).comp
        (TopModuleCat.tensorQuotient ℤ productCoefficients rightModule
          (evenRightSubmodule B)).symm.toContinuousLinearMap)

/-- Projection to the Finsupp block after quotienting the right factor. -/
private def quotientProjectD (B : Submodule ℤ ℝ) :
    let P := evenRightSubmodule B
    let φ : (H : ModuleCat ℤ) →
        TopModuleCat.Hom
          (TopModuleCat.tensorLeftObj ℤ H (TopModuleCat.of ℤ P))
          (TopModuleCat.tensorLeftObj ℤ H rightModule) :=
      fun H ↦ CategoryTheory.ConcreteCategory.ofHom
        (C := TopModuleCat ℤ)
        (X := TopModuleCat.tensorLeftObj ℤ H (TopModuleCat.of ℤ P))
        (Y := TopModuleCat.tensorLeftObj ℤ H rightModule)
        (TopModuleCat.tensorMapCLM ℤ (C := H) (D := H)
          (M := TopModuleCat.of ℤ P) (N := rightModule)
          (LinearMap.id : H →ₗ[ℤ] H) P.subtypeL)
    let Q := fun H : ModuleCat ℤ ↦ TopModuleCat.coker (φ H)
    Q productCoefficients →L[ℤ] Q finsuppCoefficients :=
  (TopModuleCat.tensorQuotient ℤ finsuppCoefficients rightModule
    (evenRightSubmodule B)).toContinuousLinearMap.comp
      ((TopModuleCat.tensorMapCLM ℤ
        (C := productCoefficients) (D := finsuppCoefficients)
        (M := TopModuleCat.of ℤ (rightModule ⧸ evenRightSubmodule B))
        (N := TopModuleCat.of ℤ (rightModule ⧸ evenRightSubmodule B))
        (LinearMap.snd ℤ torsionCoefficients finsuppCoefficients)
        (ContinuousLinearMap.id ℤ (TopModuleCat.of ℤ
          (rightModule ⧸ evenRightSubmodule B)))).comp
        (TopModuleCat.tensorQuotient ℤ productCoefficients rightModule
          (evenRightSubmodule B)).symm.toContinuousLinearMap)

/-- The algebraic torsion detector descends because even integers kill its coefficients. -/
private def quotientTorsionDetector (B : Submodule ℤ ℝ) :
    let P := evenRightSubmodule B
    let φ : TopModuleCat.Hom
        (TopModuleCat.tensorLeftObj ℤ torsionCoefficients (TopModuleCat.of ℤ P))
        torsionTensor :=
      CategoryTheory.ConcreteCategory.ofHom
        (C := TopModuleCat ℤ)
        (X := TopModuleCat.tensorLeftObj ℤ torsionCoefficients (TopModuleCat.of ℤ P))
        (Y := torsionTensor)
        (TopModuleCat.tensorMapCLM ℤ (C := torsionCoefficients) (D := torsionCoefficients)
          (M := TopModuleCat.of ℤ P) (N := rightModule)
          (LinearMap.id : torsionCoefficients →ₗ[ℤ] torsionCoefficients) P.subtypeL)
    TopModuleCat.coker φ →ₗ[ℤ] torsionCoefficients :=
  (LinearMap.range (TensorProduct.map
    (LinearMap.id : torsionCoefficients →ₗ[ℤ] torsionCoefficients)
    (evenRightSubmodule B).subtype)).liftQ torsionDetector (by
      rintro _ ⟨t, rfl⟩
      change torsionDetector (TensorProduct.map
        (LinearMap.id : torsionCoefficients →ₗ[ℤ] torsionCoefficients)
        (evenRightSubmodule B).subtype t) = 0
      have hz : torsionDetector.comp (TensorProduct.map
          (LinearMap.id : torsionCoefficients →ₗ[ℤ] torsionCoefficients)
          (evenRightSubmodule B).subtype) = 0 := by
        apply TensorProduct.ext'
        intro c m
        change torsionDetector (c ⊗ₜ[ℤ] (m : rightModule)) = 0
        rw [torsionDetector_tmul]
        have hm : m.val.1 ∈ Submodule.span ℤ {(2 : ℤ)} :=
          (Submodule.mem_prod.mp m.property).1
        obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hm
        have ha' : a * 2 = m.val.1 := by simpa only [smul_eq_mul] using ha
        rw [← ha', mul_smul, torsionCoefficients_two_smul, smul_zero]
      exact DFunLike.congr_fun hz t)

/-- The integer detector descends after reducing its output modulo two. -/
private def quotientIntegerDetector (B : Submodule ℤ ℝ) (i : ℕ) :
    let P := evenRightSubmodule B
    let φ : TopModuleCat.Hom
        (TopModuleCat.tensorLeftObj ℤ finsuppCoefficients (TopModuleCat.of ℤ P))
        finsuppTensor :=
      CategoryTheory.ConcreteCategory.ofHom
        (C := TopModuleCat ℤ)
        (X := TopModuleCat.tensorLeftObj ℤ finsuppCoefficients (TopModuleCat.of ℤ P))
        (Y := finsuppTensor)
        (TopModuleCat.tensorMapCLM ℤ (C := finsuppCoefficients) (D := finsuppCoefficients)
          (M := TopModuleCat.of ℤ P) (N := rightModule)
          (LinearMap.id : finsuppCoefficients →ₗ[ℤ] finsuppCoefficients) P.subtypeL)
    TopModuleCat.coker φ →ₗ[ℤ] ZMod 2 :=
  (LinearMap.range (TensorProduct.map
    (LinearMap.id : finsuppCoefficients →ₗ[ℤ] finsuppCoefficients)
    (evenRightSubmodule B).subtype)).liftQ
      ((Int.castAddHom (ZMod 2)).toIntLinearMap.comp (integerDetector i)) (by
        rintro _ ⟨t, rfl⟩
        change ((integerDetector i (TensorProduct.map
          (LinearMap.id : finsuppCoefficients →ₗ[ℤ] finsuppCoefficients)
          (evenRightSubmodule B).subtype t) : ℤ) : ZMod 2) = 0
        have hz : ((Int.castAddHom (ZMod 2)).toIntLinearMap.comp
            (integerDetector i)).comp (TensorProduct.map
              (LinearMap.id : finsuppCoefficients →ₗ[ℤ] finsuppCoefficients)
              (evenRightSubmodule B).subtype) = 0 := by
          apply TensorProduct.ext'
          intro d m
          change ((integerDetector i (d ⊗ₜ[ℤ] (m : rightModule)) : ℤ) : ZMod 2) = 0
          rw [integerDetector_tmul]
          apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mpr
          have hm : m.val.1 ∈ Submodule.span ℤ {(2 : ℤ)} :=
            (Submodule.mem_prod.mp m.property).1
          obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hm
          have ha' : a * 2 = m.val.1 := by simpa only [smul_eq_mul] using ha
          refine ⟨d i * a, ?_⟩
          rw [← ha']
          ring
        exact DFunLike.congr_fun hz t)

/-- The real detector descends to real numbers modulo `B`. -/
private def quotientRealDetector (B : Submodule ℤ ℝ) (i : ℕ) :
    let P := evenRightSubmodule B
    let φ : TopModuleCat.Hom
        (TopModuleCat.tensorLeftObj ℤ finsuppCoefficients (TopModuleCat.of ℤ P))
        finsuppTensor :=
      CategoryTheory.ConcreteCategory.ofHom
        (C := TopModuleCat ℤ)
        (X := TopModuleCat.tensorLeftObj ℤ finsuppCoefficients (TopModuleCat.of ℤ P))
        (Y := finsuppTensor)
        (TopModuleCat.tensorMapCLM ℤ (C := finsuppCoefficients) (D := finsuppCoefficients)
          (M := TopModuleCat.of ℤ P) (N := rightModule)
          (LinearMap.id : finsuppCoefficients →ₗ[ℤ] finsuppCoefficients) P.subtypeL)
    TopModuleCat.coker φ →ₗ[ℤ] (ℝ ⧸ B) :=
  (LinearMap.range (TensorProduct.map
    (LinearMap.id : finsuppCoefficients →ₗ[ℤ] finsuppCoefficients)
    (evenRightSubmodule B).subtype)).liftQ (B.mkQ.comp (realDetector i)) (by
      rintro _ ⟨t, rfl⟩
      change B.mkQ (realDetector i (TensorProduct.map
        (LinearMap.id : finsuppCoefficients →ₗ[ℤ] finsuppCoefficients)
        (evenRightSubmodule B).subtype t)) = 0
      have hz : (B.mkQ.comp (realDetector i)).comp (TensorProduct.map
          (LinearMap.id : finsuppCoefficients →ₗ[ℤ] finsuppCoefficients)
          (evenRightSubmodule B).subtype) = 0 := by
        apply TensorProduct.ext'
        intro d m
        change B.mkQ (realDetector i (d ⊗ₜ[ℤ] (m : rightModule))) = 0
        rw [realDetector_tmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        have hm : m.val.2 ∈ B := (Submodule.mem_prod.mp m.property).2
        simpa only [zsmul_eq_mul] using B.smul_mem (d i) hm
      exact DFunLike.congr_fun hz t)

/-- The zero and whole right submodules give the two generic quotient boundaries. -/
private theorem quotientTensor_boundaries :
    let P_b : Submodule ℤ rightModule := ⊥
    let P_t : Submodule ℤ rightModule := ⊤
    let K := fun P : Submodule ℤ rightModule ↦
      (LinearMap.range (TensorProduct.map
        (LinearMap.id : productCoefficients →ₗ[ℤ] productCoefficients) P.subtype) :
          Submodule ℤ productTensor)
    let S := fun P : Submodule ℤ rightModule ↦
      TopModuleCat.tensorLeftObj ℤ productCoefficients (TopModuleCat.of ℤ (rightModule ⧸ P))
    let φ : (P : Submodule ℤ rightModule) →
        TopModuleCat.Hom
          (TopModuleCat.tensorLeftObj ℤ productCoefficients (TopModuleCat.of ℤ P))
          productTensor :=
      fun P ↦ CategoryTheory.ConcreteCategory.ofHom
        (C := TopModuleCat ℤ)
        (X := TopModuleCat.tensorLeftObj ℤ productCoefficients (TopModuleCat.of ℤ P))
        (Y := productTensor)
        (TopModuleCat.tensorMapCLM ℤ (C := productCoefficients) (D := productCoefficients)
          (M := TopModuleCat.of ℤ P) (N := rightModule)
          (LinearMap.id : productCoefficients →ₗ[ℤ] productCoefficients) P.subtypeL)
    let Q := fun P : Submodule ℤ rightModule ↦ TopModuleCat.coker (φ P)
    let e := fun P : Submodule ℤ rightModule ↦
      TopModuleCat.tensorQuotient ℤ productCoefficients rightModule P
    K P_b = ⊥ ∧ K P_t = ⊤ ∧
    (∀ h : K P_b = ⊥,
      (e P_b).toLinearEquiv.trans ((K P_b).quotEquivOfEqBot h) =
        TensorProduct.congr (LinearEquiv.refl ℤ productCoefficients)
          ((⊥ : Submodule ℤ rightModule).quotEquivOfEqBot rfl)) ∧
    (∀ (s : S P_t) (w : Q P_t), s = 0 ∧ w = 0) ∧
    (∀ (s : S P_b) (w : Q P_b),
      (e P_b).symm (e P_b s) = s ∧ e P_b ((e P_b).symm w) = w) ∧
    (∀ (s : S P_t) (w : Q P_t),
      (e P_t).symm (e P_t s) = s ∧ e P_t ((e P_t).symm w) = w) := by
  intro P_b P_t K S φ Q e
  have hb : K P_b = ⊥ := by
    change LinearMap.range (TensorProduct.map
      (LinearMap.id : productCoefficients →ₗ[ℤ] productCoefficients) P_b.subtype) = ⊥
    calc
      _ = Submodule.map₂ (TensorProduct.mk ℤ productCoefficients rightModule)
          (LinearMap.range (LinearMap.id : productCoefficients →ₗ[ℤ] productCoefficients))
          (LinearMap.range P_b.subtype) :=
        TensorProduct.range_map
          (LinearMap.id : productCoefficients →ₗ[ℤ] productCoefficients) P_b.subtype
      _ = Submodule.map₂ (TensorProduct.mk ℤ productCoefficients rightModule) ⊤ P_b := by
        rw [LinearMap.range_id, Submodule.range_subtype]
      _ = ⊥ := Submodule.map₂_bot_right _ _
  have ht : K P_t = ⊤ := by
    change LinearMap.range (TensorProduct.map
      (LinearMap.id : productCoefficients →ₗ[ℤ] productCoefficients) P_t.subtype) = ⊤
    calc
      _ = Submodule.map₂ (TensorProduct.mk ℤ productCoefficients rightModule)
          (LinearMap.range (LinearMap.id : productCoefficients →ₗ[ℤ] productCoefficients))
          (LinearMap.range P_t.subtype) :=
        TensorProduct.range_map
          (LinearMap.id : productCoefficients →ₗ[ℤ] productCoefficients) P_t.subtype
      _ = Submodule.map₂ (TensorProduct.mk ℤ productCoefficients rightModule) ⊤ P_t := by
        rw [LinearMap.range_id, Submodule.range_subtype]
      _ = ⊤ := by
        have htop : Submodule.map₂
            (TensorProduct.mk ℤ productCoefficients rightModule) ⊤ ⊤ = ⊤ :=
          TensorProduct.map₂_mk_top_top_eq_top ℤ productCoefficients rightModule
        simpa only [P_t] using htop
  have hQ (w : Q P_t) : w = 0 := by
    obtain ⟨z, rfl⟩ := TopModuleCat.cokerπ_surjective (φ P_t) w
    change (K P_t).mkQ z = 0
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    rw [ht]
    exact Submodule.mem_top
  refine ⟨hb, ht, ?_, ?_, ?_, ?_⟩
  · intro h
    apply LinearEquiv.toLinearMap_injective
    apply TensorProduct.ext'
    intro c m
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective P_b m
    change (K P_b).quotEquivOfEqBot h
      (e P_b (c ⊗ₜ[ℤ] P_b.mkQL m)) = c ⊗ₜ[ℤ] m
    exact (congrArg ((K P_b).quotEquivOfEqBot h)
      (TopModuleCat.tensorQuotient_tmul_mkQ ℤ productCoefficients rightModule P_b c m)).trans
        (Submodule.quotEquivOfEqBot_apply_mk (K P_b) h (c ⊗ₜ[ℤ] m))
  · intro s w
    refine ⟨(e P_t).injective ?_, hQ w⟩
    exact (hQ (e P_t s)).trans (map_zero (e P_t)).symm
  · intro s w
    exact ⟨(e P_b).symm_apply_apply s, (e P_b).apply_symm_apply w⟩
  · intro s w
    exact ⟨(e P_t).symm_apply_apply s, (e P_t).apply_symm_apply w⟩

/-- All-input block agreements, diagonal and off-diagonal composites, and recoveries. -/
private theorem quotientTensor_block_values (B : Submodule ℤ ℝ) :
    let P := evenRightSubmodule B
    let φ : (H : ModuleCat ℤ) →
        TopModuleCat.Hom
          (TopModuleCat.tensorLeftObj ℤ H (TopModuleCat.of ℤ P))
          (TopModuleCat.tensorLeftObj ℤ H rightModule) :=
      fun H ↦ CategoryTheory.ConcreteCategory.ofHom
        (C := TopModuleCat ℤ)
        (X := TopModuleCat.tensorLeftObj ℤ H (TopModuleCat.of ℤ P))
        (Y := TopModuleCat.tensorLeftObj ℤ H rightModule)
        (TopModuleCat.tensorMapCLM ℤ (C := H) (D := H)
          (M := TopModuleCat.of ℤ P) (N := rightModule)
          (LinearMap.id : H →ₗ[ℤ] H) P.subtypeL)
    let S := fun H : ModuleCat ℤ ↦
      TopModuleCat.tensorLeftObj ℤ H (TopModuleCat.of ℤ (rightModule ⧸ P))
    let Q := fun H : ModuleCat ℤ ↦ TopModuleCat.coker (φ H)
    let q := fun H : ModuleCat ℤ ↦ (TopModuleCat.cokerπ (φ H)).hom
    let e := fun H : ModuleCat ℤ ↦ TopModuleCat.tensorQuotient ℤ H rightModule P
    (∀ (z : productTensor) (s : torsionTensor) (t : finsuppTensor),
      quotientProjectC B (q productCoefficients z) = q torsionCoefficients (projectC z) ∧
      quotientProjectD B (q productCoefficients z) = q finsuppCoefficients (projectD z) ∧
      quotientIncludeC B (q torsionCoefficients s) = q productCoefficients (includeC s) ∧
      quotientIncludeD B (q finsuppCoefficients t) = q productCoefficients (includeD t)) ∧
    (∀ (a : Q torsionCoefficients) (b : Q finsuppCoefficients) (w : Q productCoefficients),
      quotientProjectC B (quotientIncludeC B a) = a ∧
      quotientProjectD B (quotientIncludeD B b) = b ∧
      quotientProjectC B (quotientIncludeD B b) = 0 ∧
      quotientProjectD B (quotientIncludeC B a) = 0 ∧
      (quotientProjectC B (quotientIncludeC B a + quotientIncludeD B b),
        quotientProjectD B (quotientIncludeC B a + quotientIncludeD B b)) = (a, b) ∧
      quotientIncludeC B (quotientProjectC B w) +
        quotientIncludeD B (quotientProjectD B w) = w) ∧
    (∀ (s : S torsionCoefficients) (w : Q torsionCoefficients),
      (e torsionCoefficients).symm (e torsionCoefficients s) = s ∧
      e torsionCoefficients ((e torsionCoefficients).symm w) = w) ∧
    (∀ (s : S finsuppCoefficients) (w : Q finsuppCoefficients),
      (e finsuppCoefficients).symm (e finsuppCoefficients s) = s ∧
      e finsuppCoefficients ((e finsuppCoefficients).symm w) = w) ∧
    (∀ (s : S productCoefficients) (w : Q productCoefficients),
      (e productCoefficients).symm (e productCoefficients s) = s ∧
      e productCoefficients ((e productCoefficients).symm w) = w) := by
  intro P φ S Q q e
  have hC (z : productTensor) :
      quotientProjectC B (q productCoefficients z) =
        q torsionCoefficients (projectC z) := by
    have h : (quotientProjectC B).comp (q productCoefficients) =
        (q torsionCoefficients).comp projectC := by
      apply TopModuleCat.tensorLeft_ext ℤ
      intro p m
      rcases p with ⟨c, d⟩
      let T := TopModuleCat.tensorMapCLM ℤ
        (C := productCoefficients) (D := torsionCoefficients)
        (M := TopModuleCat.of ℤ (rightModule ⧸ P))
        (N := TopModuleCat.of ℤ (rightModule ⧸ P))
        (LinearMap.fst ℤ torsionCoefficients finsuppCoefficients)
        (ContinuousLinearMap.id ℤ (TopModuleCat.of ℤ (rightModule ⧸ P)))
      change e torsionCoefficients (T ((e productCoefficients).symm
        (q productCoefficients (((c, d) : productCoefficients) ⊗ₜ[ℤ] m)))) =
          q torsionCoefficients (projectC (((c, d) : productCoefficients) ⊗ₜ[ℤ] m))
      calc
        _ = e torsionCoefficients
            (T (((c, d) : productCoefficients) ⊗ₜ[ℤ] P.mkQL m)) :=
          congrArg (fun u ↦ e torsionCoefficients (T u))
            (TopModuleCat.tensorQuotient_symm_mkQ_tmul ℤ
              productCoefficients rightModule P (c, d) m)
        _ = e torsionCoefficients (c ⊗ₜ[ℤ] P.mkQL m) := by
          apply congrArg (e torsionCoefficients)
          simpa only [ContinuousLinearMap.id_apply, LinearMap.fst_apply] using
            (TopModuleCat.tensorMapCLM_tmul ℤ
              (C := productCoefficients) (D := torsionCoefficients)
              (M := TopModuleCat.of ℤ (rightModule ⧸ P))
              (N := TopModuleCat.of ℤ (rightModule ⧸ P))
              (LinearMap.fst ℤ torsionCoefficients finsuppCoefficients)
              (ContinuousLinearMap.id ℤ (TopModuleCat.of ℤ (rightModule ⧸ P)))
              ((c, d) : productCoefficients) (P.mkQL m))
        _ = q torsionCoefficients (c ⊗ₜ[ℤ] m) :=
          TopModuleCat.tensorQuotient_tmul_mkQ ℤ torsionCoefficients rightModule P c m
        _ = q torsionCoefficients (projectC (((c, d) : productCoefficients) ⊗ₜ[ℤ] m)) :=
          congrArg (q torsionCoefficients) (primitive_maps_tmul c d m).2.2.1.symm
    exact DFunLike.congr_fun h z
  have hD (z : productTensor) :
      quotientProjectD B (q productCoefficients z) =
        q finsuppCoefficients (projectD z) := by
    have h : (quotientProjectD B).comp (q productCoefficients) =
        (q finsuppCoefficients).comp projectD := by
      apply TopModuleCat.tensorLeft_ext ℤ
      intro p m
      rcases p with ⟨c, d⟩
      let T := TopModuleCat.tensorMapCLM ℤ
        (C := productCoefficients) (D := finsuppCoefficients)
        (M := TopModuleCat.of ℤ (rightModule ⧸ P))
        (N := TopModuleCat.of ℤ (rightModule ⧸ P))
        (LinearMap.snd ℤ torsionCoefficients finsuppCoefficients)
        (ContinuousLinearMap.id ℤ (TopModuleCat.of ℤ (rightModule ⧸ P)))
      change e finsuppCoefficients (T ((e productCoefficients).symm
        (q productCoefficients (((c, d) : productCoefficients) ⊗ₜ[ℤ] m)))) =
          q finsuppCoefficients (projectD (((c, d) : productCoefficients) ⊗ₜ[ℤ] m))
      calc
        _ = e finsuppCoefficients
            (T (((c, d) : productCoefficients) ⊗ₜ[ℤ] P.mkQL m)) :=
          congrArg (fun u ↦ e finsuppCoefficients (T u))
            (TopModuleCat.tensorQuotient_symm_mkQ_tmul ℤ
              productCoefficients rightModule P (c, d) m)
        _ = e finsuppCoefficients (d ⊗ₜ[ℤ] P.mkQL m) := by
          apply congrArg (e finsuppCoefficients)
          simpa only [ContinuousLinearMap.id_apply, LinearMap.snd_apply] using
            (TopModuleCat.tensorMapCLM_tmul ℤ
              (C := productCoefficients) (D := finsuppCoefficients)
              (M := TopModuleCat.of ℤ (rightModule ⧸ P))
              (N := TopModuleCat.of ℤ (rightModule ⧸ P))
              (LinearMap.snd ℤ torsionCoefficients finsuppCoefficients)
              (ContinuousLinearMap.id ℤ (TopModuleCat.of ℤ (rightModule ⧸ P)))
              ((c, d) : productCoefficients) (P.mkQL m))
        _ = q finsuppCoefficients (d ⊗ₜ[ℤ] m) :=
          TopModuleCat.tensorQuotient_tmul_mkQ ℤ finsuppCoefficients rightModule P d m
        _ = q finsuppCoefficients (projectD (((c, d) : productCoefficients) ⊗ₜ[ℤ] m)) :=
          congrArg (q finsuppCoefficients) (primitive_maps_tmul c d m).2.2.2.symm
    exact DFunLike.congr_fun h z
  have hIC (s : torsionTensor) :
      quotientIncludeC B (q torsionCoefficients s) =
        q productCoefficients (includeC s) := by
    have h : (quotientIncludeC B).comp (q torsionCoefficients) =
        (q productCoefficients).comp includeC := by
      apply TopModuleCat.tensorLeft_ext ℤ
      intro c m
      let T := TopModuleCat.tensorMapCLM ℤ
        (C := torsionCoefficients) (D := productCoefficients)
        (M := TopModuleCat.of ℤ (rightModule ⧸ P))
        (N := TopModuleCat.of ℤ (rightModule ⧸ P))
        (LinearMap.inl ℤ torsionCoefficients finsuppCoefficients)
        (ContinuousLinearMap.id ℤ (TopModuleCat.of ℤ (rightModule ⧸ P)))
      change e productCoefficients (T ((e torsionCoefficients).symm
        (q torsionCoefficients (c ⊗ₜ[ℤ] m)))) =
          q productCoefficients (includeC (c ⊗ₜ[ℤ] m))
      calc
        _ = e productCoefficients (T (c ⊗ₜ[ℤ] P.mkQL m)) :=
          congrArg (fun u ↦ e productCoefficients (T u))
            (TopModuleCat.tensorQuotient_symm_mkQ_tmul ℤ
              torsionCoefficients rightModule P c m)
        _ = e productCoefficients
            (((c, 0) : productCoefficients) ⊗ₜ[ℤ] P.mkQL m) := by
          apply congrArg (e productCoefficients)
          simpa only [ContinuousLinearMap.id_apply, LinearMap.inl_apply] using
            (TopModuleCat.tensorMapCLM_tmul ℤ
              (C := torsionCoefficients) (D := productCoefficients)
              (M := TopModuleCat.of ℤ (rightModule ⧸ P))
              (N := TopModuleCat.of ℤ (rightModule ⧸ P))
              (LinearMap.inl ℤ torsionCoefficients finsuppCoefficients)
              (ContinuousLinearMap.id ℤ (TopModuleCat.of ℤ (rightModule ⧸ P))) c (P.mkQL m))
        _ = q productCoefficients (((c, 0) : productCoefficients) ⊗ₜ[ℤ] m) :=
          TopModuleCat.tensorQuotient_tmul_mkQ ℤ productCoefficients rightModule P (c, 0) m
        _ = q productCoefficients (includeC (c ⊗ₜ[ℤ] m)) :=
          congrArg (q productCoefficients) (primitive_maps_tmul c 0 m).1.symm
    exact DFunLike.congr_fun h s
  have hID (t : finsuppTensor) :
      quotientIncludeD B (q finsuppCoefficients t) =
        q productCoefficients (includeD t) := by
    have h : (quotientIncludeD B).comp (q finsuppCoefficients) =
        (q productCoefficients).comp includeD := by
      apply TopModuleCat.tensorLeft_ext ℤ
      intro d m
      let T := TopModuleCat.tensorMapCLM ℤ
        (C := finsuppCoefficients) (D := productCoefficients)
        (M := TopModuleCat.of ℤ (rightModule ⧸ P))
        (N := TopModuleCat.of ℤ (rightModule ⧸ P))
        (LinearMap.inr ℤ torsionCoefficients finsuppCoefficients)
        (ContinuousLinearMap.id ℤ (TopModuleCat.of ℤ (rightModule ⧸ P)))
      change e productCoefficients (T ((e finsuppCoefficients).symm
        (q finsuppCoefficients (d ⊗ₜ[ℤ] m)))) =
          q productCoefficients (includeD (d ⊗ₜ[ℤ] m))
      calc
        _ = e productCoefficients (T (d ⊗ₜ[ℤ] P.mkQL m)) :=
          congrArg (fun u ↦ e productCoefficients (T u))
            (TopModuleCat.tensorQuotient_symm_mkQ_tmul ℤ
              finsuppCoefficients rightModule P d m)
        _ = e productCoefficients
            (((0, d) : productCoefficients) ⊗ₜ[ℤ] P.mkQL m) := by
          apply congrArg (e productCoefficients)
          simpa only [ContinuousLinearMap.id_apply, LinearMap.inr_apply] using
            (TopModuleCat.tensorMapCLM_tmul ℤ
              (C := finsuppCoefficients) (D := productCoefficients)
              (M := TopModuleCat.of ℤ (rightModule ⧸ P))
              (N := TopModuleCat.of ℤ (rightModule ⧸ P))
              (LinearMap.inr ℤ torsionCoefficients finsuppCoefficients)
              (ContinuousLinearMap.id ℤ (TopModuleCat.of ℤ (rightModule ⧸ P))) d (P.mkQL m))
        _ = q productCoefficients (((0, d) : productCoefficients) ⊗ₜ[ℤ] m) :=
          TopModuleCat.tensorQuotient_tmul_mkQ ℤ productCoefficients rightModule P (0, d) m
        _ = q productCoefficients (includeD (d ⊗ₜ[ℤ] m)) :=
          congrArg (q productCoefficients) (primitive_maps_tmul 0 d m).2.1.symm
    exact DFunLike.congr_fun h t
  refine ⟨(fun z s t ↦ ⟨hC z, hD z, hIC s, hID t⟩), ?_, ?_, ?_, ?_⟩
  · intro a b w
    obtain ⟨s, rfl⟩ := TopModuleCat.cokerπ_surjective (φ torsionCoefficients) a
    obtain ⟨t, rfl⟩ := TopModuleCat.cokerπ_surjective (φ finsuppCoefficients) b
    obtain ⟨z, rfl⟩ := TopModuleCat.cokerπ_surjective (φ productCoefficients) w
    have hv := projection_inclusion_values s t
    have hcc : quotientProjectC B (quotientIncludeC B (q torsionCoefficients s)) =
        q torsionCoefficients s := by
      rw [hIC, hC, hv.1]
    have hdd : quotientProjectD B (quotientIncludeD B (q finsuppCoefficients t)) =
        q finsuppCoefficients t := by
      rw [hID, hD, hv.2.1]
    have hcd : quotientProjectC B (quotientIncludeD B (q finsuppCoefficients t)) = 0 := by
      rw [hID, hC, hv.2.2.1, map_zero]
    have hdc : quotientProjectD B (quotientIncludeC B (q torsionCoefficients s)) = 0 := by
      rw [hIC, hD, hv.2.2.2, map_zero]
    refine ⟨hcc, hdd, hcd, hdc, ?_, ?_⟩
    · apply Prod.ext
      · calc
          _ = quotientProjectC B (quotientIncludeC B (q torsionCoefficients s)) +
              quotientProjectC B (quotientIncludeD B (q finsuppCoefficients t)) :=
            map_add (quotientProjectC B) _ _
          _ = q torsionCoefficients s + 0 :=
            congrArg₂ (fun x y : Q torsionCoefficients ↦ x + y) hcc hcd
          _ = q torsionCoefficients s := add_zero _
      · calc
          _ = quotientProjectD B (quotientIncludeC B (q torsionCoefficients s)) +
              quotientProjectD B (quotientIncludeD B (q finsuppCoefficients t)) :=
            map_add (quotientProjectD B) _ _
          _ = 0 + q finsuppCoefficients t :=
            congrArg₂ (fun x y : Q finsuppCoefficients ↦ x + y) hdc hdd
          _ = q finsuppCoefficients t := zero_add _
    · calc
        _ = quotientIncludeC B (q torsionCoefficients (projectC z)) +
            quotientIncludeD B (q finsuppCoefficients (projectD z)) :=
          congrArg₂ (fun x y : Q productCoefficients ↦ x + y)
            (congrArg (quotientIncludeC B) (hC z))
            (congrArg (quotientIncludeD B) (hD z))
        _ = q productCoefficients (includeC (projectC z)) +
            q productCoefficients (includeD (projectD z)) :=
          congrArg₂ (fun x y : Q productCoefficients ↦ x + y) (hIC _) (hID _)
        _ = q productCoefficients (includeC (projectC z) + includeD (projectD z)) :=
          (map_add (q productCoefficients) _ _).symm
        _ = q productCoefficients z := congrArg (q productCoefficients) (reconstruct z)
  · intro s w
    exact ⟨(e torsionCoefficients).symm_apply_apply s,
      (e torsionCoefficients).apply_symm_apply w⟩
  · intro s w
    exact ⟨(e finsuppCoefficients).symm_apply_apply s,
      (e finsuppCoefficients).apply_symm_apply w⟩
  · intro s w
    exact ⟨(e productCoefficients).symm_apply_apply s,
      (e productCoefficients).apply_symm_apply w⟩

/-- All-input detector formulas, including every off-index zero and torsion-real zero. -/
private theorem quotientTensor_detector_values (B : Submodule ℤ ℝ) :
    let P := evenRightSubmodule B
    let φ : (H : ModuleCat ℤ) →
        TopModuleCat.Hom
          (TopModuleCat.tensorLeftObj ℤ H (TopModuleCat.of ℤ P))
          (TopModuleCat.tensorLeftObj ℤ H rightModule) :=
      fun H ↦ CategoryTheory.ConcreteCategory.ofHom
        (C := TopModuleCat ℤ)
        (X := TopModuleCat.tensorLeftObj ℤ H (TopModuleCat.of ℤ P))
        (Y := TopModuleCat.tensorLeftObj ℤ H rightModule)
        (TopModuleCat.tensorMapCLM ℤ (C := H) (D := H)
          (M := TopModuleCat.of ℤ P) (N := rightModule)
          (LinearMap.id : H →ₗ[ℤ] H) P.subtypeL)
    let q := fun H : ModuleCat ℤ ↦ (TopModuleCat.cokerπ (φ H)).hom
    (∀ (s : torsionTensor) (t : finsuppTensor) (i : ℕ),
      quotientTorsionDetector B (q torsionCoefficients s) = torsionDetector s ∧
      quotientIntegerDetector B i (q finsuppCoefficients t) =
        (Int.castAddHom (ZMod 2)).toIntLinearMap (integerDetector i t) ∧
      quotientRealDetector B i (q finsuppCoefficients t) = B.mkQ (realDetector i t)) ∧
    (∀ (c : torsionCoefficients) (d : finsuppCoefficients) (a : ℤ) (x : ℝ) (i : ℕ),
      quotientTorsionDetector B (q torsionCoefficients
        (c ⊗ₜ[ℤ] ((a, x) : rightModule))) = a • c ∧
      quotientIntegerDetector B i (q finsuppCoefficients
        (d ⊗ₜ[ℤ] ((a, x) : rightModule))) =
          (Int.castAddHom (ZMod 2)).toIntLinearMap (d i * a) ∧
      quotientRealDetector B i (q finsuppCoefficients
        (d ⊗ₜ[ℤ] ((a, x) : rightModule))) = B.mkQ ((d i : ℝ) * x) ∧
      q torsionCoefficients (c ⊗ₜ[ℤ] ((0, x) : rightModule)) = 0) ∧
    (∀ (i n : ℕ) (x : ℝ),
      quotientIntegerDetector B i (q finsuppCoefficients (w n)) =
        (if i = n then 1 else 0) ∧
      quotientRealDetector B i (q finsuppCoefficients (w n)) = 0 ∧
      quotientIntegerDetector B i (q finsuppCoefficients (v n x)) = 0 ∧
      quotientRealDetector B i (q finsuppCoefficients (v n x)) =
        (if i = n then B.mkQ x else 0)) := by
  intro P φ q
  have hT (s : torsionTensor) :
      quotientTorsionDetector B (q torsionCoefficients s) = torsionDetector s := by
    rfl
  have hI (i : ℕ) (t : finsuppTensor) :
      quotientIntegerDetector B i (q finsuppCoefficients t) =
        (Int.castAddHom (ZMod 2)).toIntLinearMap (integerDetector i t) := by
    rfl
  have hR (i : ℕ) (t : finsuppTensor) :
      quotientRealDetector B i (q finsuppCoefficients t) = B.mkQ (realDetector i t) := by
    rfl
  refine ⟨(fun s t i ↦ ⟨hT s, hI i t, hR i t⟩), ?_, ?_⟩
  · intro c d a x i
    refine ⟨(hT _).trans (torsionDetector_tmul c a x),
      (hI i _).trans (congrArg (Int.castAddHom (ZMod 2)).toIntLinearMap
        (integerDetector_tmul i d a x)),
      (hR i _).trans (congrArg B.mkQ (realDetector_tmul i d a x)), ?_⟩
    exact (congrArg (q torsionCoefficients) (torsionTensor_real_annihilated c x)).trans
      (map_zero (q torsionCoefficients))
  · intro i n x
    classical
    refine ⟨?_, ?_, ?_, ?_⟩
    · calc
        _ = (Int.castAddHom (ZMod 2)).toIntLinearMap
            ((Finsupp.single n (1 : ℤ)) i * 1) :=
          (hI i (w n)).trans
            (congrArg (Int.castAddHom (ZMod 2)).toIntLinearMap
              (integerDetector_tmul i (Finsupp.single n 1) 1 0))
        _ = (if i = n then 1 else 0) := by
          by_cases h : i = n <;> simp [h]
    · have hwR : realDetector i (w n) = 0 :=
        (realDetector_tmul i (Finsupp.single n 1) 1 0).trans (mul_zero _)
      exact (hR i (w n)).trans ((congrArg B.mkQ hwR).trans (map_zero B.mkQ))
    · have hvI : integerDetector i (v n x) = 0 :=
        (integerDetector_tmul i (Finsupp.single n 1) 0 x).trans (mul_zero _)
      exact (hI i (v n x)).trans
        ((congrArg (Int.castAddHom (ZMod 2)).toIntLinearMap hvI).trans
          (map_zero (Int.castAddHom (ZMod 2)).toIntLinearMap))
    · refine (hR i (v n x)).trans ((congrArg B.mkQ (realDetector_v i n x)).trans ?_)
      by_cases h : i = n <;> simp [h]

/-- Mixed sums retain the two torsion directions and independently indexed real classes. -/
private theorem quotientTensor_mixed_controls (B : Submodule ℤ ℝ) :
    let P := evenRightSubmodule B
    let φ : (H : ModuleCat ℤ) →
        TopModuleCat.Hom
          (TopModuleCat.tensorLeftObj ℤ H (TopModuleCat.of ℤ P))
          (TopModuleCat.tensorLeftObj ℤ H rightModule) :=
      fun H ↦ CategoryTheory.ConcreteCategory.ofHom
        (C := TopModuleCat ℤ)
        (X := TopModuleCat.tensorLeftObj ℤ H (TopModuleCat.of ℤ P))
        (Y := TopModuleCat.tensorLeftObj ℤ H rightModule)
        (TopModuleCat.tensorMapCLM ℤ (C := H) (D := H)
          (M := TopModuleCat.of ℤ P) (N := rightModule)
          (LinearMap.id : H →ₗ[ℤ] H) P.subtypeL)
    let q := fun H : ModuleCat ℤ ↦ (TopModuleCat.cokerπ (φ H)).hom
    let e := fun H : ModuleCat ℤ ↦ TopModuleCat.tensorQuotient ℤ H rightModule P
    ∀ (n k : ℕ), n ≠ k → ∀ (x y : ℝ), B.mkQ x ≠ 0 → B.mkQ y ≠ 0 →
    let U := q torsionCoefficients (u0 + u1)
    let V := q finsuppCoefficients (w n + v n x + v k y)
    let W := q productCoefficients (includeC (u0 + u1) + includeD (w n + v n x + v k y))
    q torsionCoefficients u0 ≠ 0 ∧ q torsionCoefficients u1 ≠ 0 ∧
    q torsionCoefficients u0 ≠ q torsionCoefficients u1 ∧
    q torsionCoefficients u0 + q torsionCoefficients u1 ≠ 0 ∧
    q finsuppCoefficients (w n) ≠ 0 ∧
    q finsuppCoefficients (v n x) ≠ 0 ∧ q finsuppCoefficients (v k y) ≠ 0 ∧
    q finsuppCoefficients (v n x) ≠ q finsuppCoefficients (v k y) ∧
    (quotientProjectC B W, quotientProjectD B W) = (U, V) ∧
    quotientIncludeC B U + quotientIncludeD B V = W ∧
    (quotientTorsionDetector B U, quotientIntegerDetector B n V,
      quotientRealDetector B n V, quotientRealDetector B k V) =
        (c0 + c1, (1 : ZMod 2), B.mkQ x, B.mkQ y) ∧
    U ≠ 0 ∧ V ≠ 0 ∧ W ≠ 0 ∧
    W ≠ quotientIncludeC B U ∧ W ≠ quotientIncludeD B V ∧
    P ≠ ⊥ ∧ P ≠ ⊤ ∧
    q finsuppCoefficients ((2 : ℤ) • w n) = 0 ∧ (2 : ℤ) • w n ≠ 0 ∧
    (e torsionCoefficients).symm U =
      TopModuleCat.tensorMapCLM ℤ (C := torsionCoefficients) (D := torsionCoefficients)
        (M := rightModule) (N := TopModuleCat.of ℤ (rightModule ⧸ P))
        (LinearMap.id : torsionCoefficients →ₗ[ℤ] torsionCoefficients) P.mkQL (u0 + u1) ∧
    (e finsuppCoefficients).symm V =
      TopModuleCat.tensorMapCLM ℤ (C := finsuppCoefficients) (D := finsuppCoefficients)
        (M := rightModule) (N := TopModuleCat.of ℤ (rightModule ⧸ P))
        (LinearMap.id : finsuppCoefficients →ₗ[ℤ] finsuppCoefficients) P.mkQL
          (w n + v n x + v k y) ∧
    (e productCoefficients).symm W =
      TopModuleCat.tensorMapCLM ℤ (C := productCoefficients) (D := productCoefficients)
        (M := rightModule) (N := TopModuleCat.of ℤ (rightModule ⧸ P))
        (LinearMap.id : productCoefficients →ₗ[ℤ] productCoefficients) P.mkQL
          (includeC (u0 + u1) + includeD (w n + v n x + v k y)) ∧
    e torsionCoefficients ((e torsionCoefficients).symm U) = U ∧
    e finsuppCoefficients ((e finsuppCoefficients).symm V) = V ∧
    e productCoefficients ((e productCoefficients).symm W) = W := by
  classical
  intro P φ q e n k hnk x y hx hy U V W
  rcases quotientTensor_detector_values B with ⟨hd, ht, hs⟩
  have h0 : quotientTorsionDetector B (q torsionCoefficients u0) = c0 := by
    simpa only [u0, one_smul] using (ht c0 0 1 0 n).1
  have h1 : quotientTorsionDetector B (q torsionCoefficients u1) = c1 := by
    simpa only [u1, one_smul] using (ht c1 0 1 0 n).1
  have hU : quotientTorsionDetector B U = c0 + c1 :=
    (congrArg (quotientTorsionDetector B)
      (map_add (q torsionCoefficients) u0 u1)).trans
        ((map_add (quotientTorsionDetector B) _ _).trans
          (congrArg₂ (fun a b : torsionCoefficients ↦ a + b) h0 h1))
  have hsum : V = q finsuppCoefficients (w n) +
      q finsuppCoefficients (v n x) + q finsuppCoefficients (v k y) :=
    (map_add (q finsuppCoefficients) (w n + v n x) (v k y)).trans
      (congrArg (fun a ↦ a + q finsuppCoefficients (v k y))
        (map_add (q finsuppCoefficients) (w n) (v n x)))
  have hiw : quotientIntegerDetector B n (q finsuppCoefficients (w n)) = 1 :=
    (hs n n 0).1.trans (ite_eq_left rfl)
  have hivn : quotientIntegerDetector B n (q finsuppCoefficients (v n x)) = 0 :=
    (hs n n x).2.2.1
  have hivk : quotientIntegerDetector B n (q finsuppCoefficients (v k y)) = 0 :=
    (hs n k y).2.2.1
  have hi : quotientIntegerDetector B n V = 1 :=
    (congrArg (quotientIntegerDetector B n) hsum).trans (by
      rw [map_add, map_add, hiw, hivn, hivk, add_zero, add_zero])
  have hrnw : quotientRealDetector B n (q finsuppCoefficients (w n)) = 0 :=
    (hs n n 0).2.1
  have hrnvn : quotientRealDetector B n (q finsuppCoefficients (v n x)) = B.mkQ x :=
    (hs n n x).2.2.2.trans (ite_eq_left rfl)
  have hrnvk : quotientRealDetector B n (q finsuppCoefficients (v k y)) = 0 :=
    (hs n k y).2.2.2.trans (ite_eq_right hnk)
  have hrkw : quotientRealDetector B k (q finsuppCoefficients (w n)) = 0 :=
    (hs k n 0).2.1
  have hrkvn : quotientRealDetector B k (q finsuppCoefficients (v n x)) = 0 :=
    (hs k n x).2.2.2.trans (ite_eq_right hnk.symm)
  have hrkvk : quotientRealDetector B k (q finsuppCoefficients (v k y)) = B.mkQ y :=
    (hs k k y).2.2.2.trans (ite_eq_left rfl)
  have hrn : quotientRealDetector B n V = B.mkQ x :=
    (congrArg (quotientRealDetector B n) hsum).trans (by
      rw [map_add, map_add, hrnw, hrnvn, hrnvk, zero_add, add_zero])
  have hrk : quotientRealDetector B k V = B.mkQ y :=
    (congrArg (quotientRealDetector B k) hsum).trans (by
      rw [map_add, map_add, hrkw, hrkvn, hrkvk, zero_add, zero_add])
  have hn0 : q finsuppCoefficients (w n) ≠ 0 := by
    intro hz
    exact one_ne_zero (hiw.symm.trans
      ((congrArg (quotientIntegerDetector B n) hz).trans (map_zero _)))
  have hvn : q finsuppCoefficients (v n x) ≠ 0 := by
    intro hz
    exact hx (hrnvn.symm.trans
      ((congrArg (quotientRealDetector B n) hz).trans (map_zero _)))
  have hvk : q finsuppCoefficients (v k y) ≠ 0 := by
    intro hz
    exact hy (hrkvk.symm.trans
      ((congrArg (quotientRealDetector B k) hz).trans (map_zero _)))
  have hvnk : q finsuppCoefficients (v n x) ≠ q finsuppCoefficients (v k y) := by
    intro hz
    exact hx (hrnvn.symm.trans
      ((congrArg (quotientRealDetector B n) hz).trans hrnvk))
  have hU0 : U ≠ 0 := by
    intro hz
    apply coefficient_controls.2.2.2
    exact hU.symm.trans ((congrArg (quotientTorsionDetector B) hz).trans (map_zero _))
  have hV0 : V ≠ 0 := by
    intro hz
    have hh : (1 : ZMod 2) = 0 :=
      hi.symm.trans ((congrArg (quotientIntegerDetector B n) hz).trans (map_zero _))
    exact one_ne_zero hh
  rcases quotientTensor_block_values B with ⟨hb, hc, hrecC, hrecD, hrecA⟩
  have hCW : quotientProjectC B W = U :=
    (hb _ (u0 + u1) (w n + v n x + v k y)).1.trans
      (congrArg (q torsionCoefficients) (mixed_projections _ _).1)
  have hDW : quotientProjectD B W = V :=
    (hb _ (u0 + u1) (w n + v n x + v k y)).2.1.trans
      (congrArg (q finsuppCoefficients) (mixed_projections _ _).2)
  have hW : quotientIncludeC B U + quotientIncludeD B V = W := by
    rw [← hCW, ← hDW]
    exact (hc U V W).2.2.2.2.2
  have hW0 : W ≠ 0 := by
    intro hz
    apply hU0
    exact hCW.symm.trans ((congrArg (quotientProjectC B) hz).trans (map_zero _))
  have hWC : W ≠ quotientIncludeC B U := by
    intro hz
    apply hV0
    exact hDW.symm.trans ((congrArg (quotientProjectD B) hz).trans (hc U V W).2.2.2.1)
  have hWD : W ≠ quotientIncludeD B V := by
    intro hz
    apply hU0
    exact hCW.symm.trans ((congrArg (quotientProjectC B) hz).trans (hc U V W).2.2.1)
  have hm2 : ((2, 0) : rightModule) ∈ P := by
    exact Submodule.mem_prod.mpr
      ⟨Submodule.mem_span_singleton_self (2 : ℤ), B.zero_mem⟩
  have hP0 : P ≠ ⊥ := by
    intro hz
    have hh : ((2, 0) : rightModule) = 0 := by simpa only [hz, Submodule.mem_bot] using hm2
    have hh' := congrArg Prod.fst hh
    norm_num at hh'
  have hPt : P ≠ ⊤ := by
    intro hz
    have hh : ((0, x) : rightModule) ∈ P := hz.symm ▸ Submodule.mem_top
    have hxB : x ∈ B := (Submodule.mem_prod.mp hh).2
    exact hx ((Submodule.Quotient.mk_eq_zero B).mpr hxB)
  have h2w : (2 : ℤ) • w n =
      (Finsupp.single n 1 : finsuppCoefficients) ⊗ₜ[ℤ] ((2, 0) : rightModule) := by
    let d : finsuppCoefficients := Finsupp.single n 1
    let a : rightModule := (1, 0)
    let G : rightModule →L[ℤ] finsuppTensor :=
      TopModuleCat.tensorGenerator ℤ finsuppCoefficients rightModule d
    have hG (m : rightModule) : G m = d ⊗ₜ[ℤ] m :=
      TopModuleCat.tensorGenerator_apply ℤ finsuppCoefficients rightModule d m
    have hGa : G a = w n := hG a
    have haa : a + a = ((2, 0) : rightModule) :=
      (@two_smul ℤ rightModule inferInstance
        rightModule.toModuleCat.isAddCommGroup.toAddCommMonoid
        rightModule.toModuleCat.isModule a).symm.trans
          rightModule_action_controls.2.1
    have htwo : (2 : ℤ) • w n = w n + w n :=
      @two_smul ℤ finsuppTensor inferInstance
        finsuppTensor.toModuleCat.isAddCommGroup.toAddCommMonoid
        finsuppTensor.toModuleCat.isModule (w n)
    have hadd : w n + w n = G a + G a :=
      congrArg₂ (fun u v : finsuppTensor ↦ u + v) hGa.symm hGa.symm
    have hmap : G a + G a = G (a + a) := (G.map_add a a).symm
    have harg : G (a + a) = G ((2, 0) : rightModule) := congrArg G haa
    have hpure : G ((2, 0) : rightModule) =
        (Finsupp.single n 1 : finsuppCoefficients) ⊗ₜ[ℤ] ((2, 0) : rightModule) :=
      hG ((2, 0) : rightModule)
    exact htwo.trans (hadd.trans (hmap.trans (harg.trans hpure)))
  have hkill : q finsuppCoefficients ((2 : ℤ) • w n) = 0 := by
    let z : TopModuleCat.tensorLeftObj ℤ finsuppCoefficients (TopModuleCat.of ℤ P) :=
      (Finsupp.single n 1 : finsuppCoefficients) ⊗ₜ[ℤ] (⟨(2, 0), hm2⟩ : P)
    have himage : (φ finsuppCoefficients).hom z =
        (Finsupp.single n 1 : finsuppCoefficients) ⊗ₜ[ℤ] ((2, 0) : rightModule) :=
      TopModuleCat.tensorMapCLM_tmul ℤ
        (C := finsuppCoefficients) (D := finsuppCoefficients)
        (M := TopModuleCat.of ℤ P) (N := rightModule)
        (LinearMap.id : finsuppCoefficients →ₗ[ℤ] finsuppCoefficients)
        P.subtypeL (Finsupp.single n 1) (⟨(2, 0), hm2⟩ : P)
    have hz : q finsuppCoefficients ((φ finsuppCoefficients).hom z) = 0 :=
      CategoryTheory.ConcreteCategory.congr_hom
        (TopModuleCat.comp_cokerπ (φ finsuppCoefficients)) z
    exact (congrArg (q finsuppCoefficients) h2w).trans
      ((congrArg (q finsuppCoefficients) himage.symm).trans hz)
  have h2ne : (2 : ℤ) • w n ≠ 0 := by
    intro hz
    have hh := congrArg (integerDetector n) hz
    rw [map_smul, (finsuppTensor_right_controls n 0).1, map_zero] at hh
    norm_num at hh
  refine ⟨?_, ?_, ?_, ?_, hn0, hvn, hvk, hvnk, Prod.ext hCW hDW, hW,
    ?_, hU0, hV0, hW0, hWC, hWD, hP0, hPt, hkill, h2ne,
    TopModuleCat.tensorQuotient_symm_mkQ ℤ torsionCoefficients rightModule P _,
    TopModuleCat.tensorQuotient_symm_mkQ ℤ finsuppCoefficients rightModule P _,
    TopModuleCat.tensorQuotient_symm_mkQ ℤ productCoefficients rightModule P _,
    (e torsionCoefficients).apply_symm_apply U,
    (e finsuppCoefficients).apply_symm_apply V,
    (e productCoefficients).apply_symm_apply W⟩
  · intro hz
    exact coefficient_controls.1
      (h0.symm.trans ((congrArg (quotientTorsionDetector B) hz).trans (map_zero _)))
  · intro hz
    exact coefficient_controls.2.1
      (h1.symm.trans ((congrArg (quotientTorsionDetector B) hz).trans (map_zero _)))
  · intro hz
    exact coefficient_controls.2.2.1
      (h0.symm.trans ((congrArg (quotientTorsionDetector B) hz).trans h1))
  · simpa only [U, map_add] using hU0
  · exact Prod.ext hU (Prod.ext hi (Prod.ext hrn hrk))

/-- Independent coefficient maps and every submodule-preserving continuous right map. -/
private theorem quotientTensor_mapped_values (B : Submodule ℤ ℝ)
    (f : torsionCoefficients →ₗ[ℤ] torsionCoefficients)
    (g : finsuppCoefficients →ₗ[ℤ] finsuppCoefficients)
    (h : rightModule →L[ℤ] rightModule)
    (hh : evenRightSubmodule B ≤ (evenRightSubmodule B).comap h.toLinearMap) :
    let P := evenRightSubmodule B
    let Mbar := TopModuleCat.of ℤ (rightModule ⧸ P)
    let hbar := P.liftQL (P.mkQL.comp h) (by
      intro m hm
      change P.mkQ (h m) = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hh hm)
    let φ : (H : ModuleCat ℤ) →
        TopModuleCat.Hom
          (TopModuleCat.tensorLeftObj ℤ H (TopModuleCat.of ℤ P))
          (TopModuleCat.tensorLeftObj ℤ H rightModule) :=
      fun H ↦ CategoryTheory.ConcreteCategory.ofHom
        (C := TopModuleCat ℤ)
        (X := TopModuleCat.tensorLeftObj ℤ H (TopModuleCat.of ℤ P))
        (Y := TopModuleCat.tensorLeftObj ℤ H rightModule)
        (TopModuleCat.tensorMapCLM ℤ (C := H) (D := H)
          (M := TopModuleCat.of ℤ P) (N := rightModule)
          (LinearMap.id : H →ₗ[ℤ] H) P.subtypeL)
    let Q := fun H : ModuleCat ℤ ↦ TopModuleCat.coker (φ H)
    let q := fun H : ModuleCat ℤ ↦ (TopModuleCat.cokerπ (φ H)).hom
    let e := fun H : ModuleCat ℤ ↦ TopModuleCat.tensorQuotient ℤ H rightModule P
    let V : (H : ModuleCat ℤ) →
        (H →ₗ[ℤ] H) → (Q H ⟶ Q H) :=
      fun (H : ModuleCat ℤ) (l : H →ₗ[ℤ] H) ↦
        CategoryTheory.CategoryStruct.comp
          (X := Q H) (Y := TopModuleCat.tensorLeftObj ℤ H Mbar) (Z := Q H)
          (CategoryTheory.CategoryStruct.comp
            (X := Q H) (Y := TopModuleCat.tensorLeftObj ℤ H Mbar)
            (Z := TopModuleCat.tensorLeftObj ℤ H Mbar)
            (TopModuleCat.ofIso (R := ℤ)
              (X := TopModuleCat.tensorLeftObj ℤ H Mbar) (Y := Q H)
              (e H)).inv
            (CategoryTheory.ConcreteCategory.ofHom
              (C := TopModuleCat ℤ)
              (X := TopModuleCat.tensorLeftObj ℤ H Mbar)
              (Y := TopModuleCat.tensorLeftObj ℤ H Mbar)
              (TopModuleCat.tensorMapCLM ℤ (C := H) (D := H)
                (M := Mbar) (N := Mbar) l hbar)))
          (TopModuleCat.ofIso (R := ℤ)
            (X := TopModuleCat.tensorLeftObj ℤ H Mbar) (Y := Q H)
            (e H)).hom
    (∀ z : torsionTensor, V torsionCoefficients f (q torsionCoefficients z) =
      q torsionCoefficients (TopModuleCat.tensorMapCLM ℤ
        (C := torsionCoefficients) (D := torsionCoefficients)
        (M := rightModule) (N := rightModule) f h z)) ∧
    (∀ z : finsuppTensor, V finsuppCoefficients g (q finsuppCoefficients z) =
      q finsuppCoefficients (TopModuleCat.tensorMapCLM ℤ
        (C := finsuppCoefficients) (D := finsuppCoefficients)
        (M := rightModule) (N := rightModule) g h z)) ∧
    (∀ z : productTensor, V productCoefficients (f.prodMap g) (q productCoefficients z) =
      q productCoefficients (TopModuleCat.tensorMapCLM ℤ
        (C := productCoefficients) (D := productCoefficients)
        (M := rightModule) (N := rightModule) (f.prodMap g) h z)) ∧
    (∀ w : Q productCoefficients,
      (quotientProjectC B (V productCoefficients (f.prodMap g) w),
        quotientProjectD B (V productCoefficients (f.prodMap g) w)) =
      (V torsionCoefficients f (quotientProjectC B w),
        V finsuppCoefficients g (quotientProjectD B w))) ∧
    (∀ (a : Q torsionCoefficients) (b : Q finsuppCoefficients),
      V productCoefficients (f.prodMap g) (quotientIncludeC B a + quotientIncludeD B b) =
        quotientIncludeC B (V torsionCoefficients f a) +
          quotientIncludeD B (V finsuppCoefficients g b)) ∧
    (∀ (n k : ℕ) (x y : ℝ),
      let W := q productCoefficients
        (includeC (u0 + u1) + includeD (w n + v n x + v k y))
      (quotientProjectC B (V productCoefficients (f.prodMap g) W),
        quotientProjectD B (V productCoefficients (f.prodMap g) W)) =
      (q torsionCoefficients (TopModuleCat.tensorMapCLM ℤ
        (C := torsionCoefficients) (D := torsionCoefficients)
        (M := rightModule) (N := rightModule) f h (u0 + u1)),
        q finsuppCoefficients (TopModuleCat.tensorMapCLM ℤ
          (C := finsuppCoefficients) (D := finsuppCoefficients)
          (M := rightModule) (N := rightModule) g h
          (w n + v n x + v k y)))) := by
  intro P Mbar hbar φ Q q e V
  let T := fun (H : ModuleCat ℤ) (l : H →ₗ[ℤ] H) ↦
    TopModuleCat.tensorMapCLM ℤ (C := H) (D := H)
      (M := rightModule) (N := rightModule) l h
  have hhbar : hbar.comp P.mkQL = P.mkQL.comp h := by
    apply ContinuousLinearMap.coe_injective
    change (P.liftQ (P.mkQL.comp h).toLinearMap _).comp P.mkQ =
      (P.mkQL.comp h).toLinearMap
    exact P.liftQ_mkQ (P.mkQL.comp h).toLinearMap _
  have hV (H : ModuleCat ℤ) (l : H →ₗ[ℤ] H)
      (z : TopModuleCat.tensorLeftObj ℤ H rightModule) :
      V H l (q H z) = q H (T H l z) := by
    let X := TopModuleCat.tensorLeftObj ℤ H rightModule
    let S := TopModuleCat.tensorLeftObj ℤ H Mbar
    let E : S ≅ Q H := TopModuleCat.ofIso (R := ℤ) (X := S) (Y := Q H) (e H)
    let F : X ⟶ S := CategoryTheory.ConcreteCategory.ofHom
      (C := TopModuleCat ℤ) (X := X) (Y := S)
      (TopModuleCat.tensorMapCLM ℤ (C := H) (D := H)
        (M := rightModule) (N := Mbar) LinearMap.id P.mkQL)
    have hFE : CategoryTheory.CategoryStruct.comp
        (X := X) (Y := S) (Z := Q H) F E.hom = TopModuleCat.cokerπ (φ H) := by
      apply CategoryTheory.ConcreteCategory.ext_apply
      intro t
      exact TopModuleCat.tensorQuotient_tensorMapCLM ℤ H rightModule P t
    have hcomm :
        (TopModuleCat.tensorMapCLM ℤ (C := H) (D := H)
          (M := Mbar) (N := Mbar) l hbar).comp
          (TopModuleCat.tensorMapCLM ℤ (C := H) (D := H)
            (M := rightModule) (N := Mbar) LinearMap.id P.mkQL) =
        (TopModuleCat.tensorMapCLM ℤ (C := H) (D := H)
          (M := rightModule) (N := Mbar) LinearMap.id P.mkQL).comp (T H l) := by
      rw [← TopModuleCat.tensorMapCLM_comp, ← TopModuleCat.tensorMapCLM_comp, hhbar]
      simp only [LinearMap.comp_id, LinearMap.id_comp]
    let U : S ⟶ S := CategoryTheory.ConcreteCategory.ofHom
      (C := TopModuleCat ℤ) (X := S) (Y := S)
      (TopModuleCat.tensorMapCLM ℤ (C := H) (D := H)
        (M := Mbar) (N := Mbar) l hbar)
    let A : X ⟶ X := CategoryTheory.ConcreteCategory.ofHom
      (C := TopModuleCat ℤ) (X := X) (Y := X) (T H l)
    have hcommCat : CategoryTheory.CategoryStruct.comp F U =
        CategoryTheory.CategoryStruct.comp A F := by
      apply CategoryTheory.ConcreteCategory.ext
      exact hcomm
    have hVcat : CategoryTheory.CategoryStruct.comp (TopModuleCat.cokerπ (φ H)) (V H l) =
        CategoryTheory.CategoryStruct.comp A (TopModuleCat.cokerπ (φ H)) := by
      change CategoryTheory.CategoryStruct.comp (TopModuleCat.cokerπ (φ H))
        (CategoryTheory.CategoryStruct.comp
          (CategoryTheory.CategoryStruct.comp E.inv U) E.hom) = _
      rw [← hFE]
      calc
        _ = CategoryTheory.CategoryStruct.comp
            (CategoryTheory.CategoryStruct.comp F
              (CategoryTheory.CategoryStruct.comp E.hom E.inv))
            (CategoryTheory.CategoryStruct.comp U E.hom) := by
          simp only [CategoryTheory.Category.assoc]
        _ = CategoryTheory.CategoryStruct.comp
            (CategoryTheory.CategoryStruct.comp F U) E.hom := by
          rw [E.hom_inv_id, CategoryTheory.Category.comp_id, CategoryTheory.Category.assoc]
        _ = CategoryTheory.CategoryStruct.comp A
            (CategoryTheory.CategoryStruct.comp F E.hom) := by
          rw [hcommCat, CategoryTheory.Category.assoc]
    have hVpoint :=
      congrArg (fun b : (X ⟶ Q H) ↦ TopModuleCat.Hom.hom b z) hVcat
    simpa only [TopModuleCat.hom_comp, q, A, CategoryTheory.ConcreteCategory.hom_ofHom,
      ContinuousLinearMap.comp_apply] using hVpoint
  have hp (z : productTensor) :
      (projectC (T productCoefficients (f.prodMap g) z),
        projectD (T productCoefficients (f.prodMap g) z)) =
      (T torsionCoefficients f (projectC z), T finsuppCoefficients g (projectD z)) := by
    have hh := DFunLike.congr_fun (tensorProdLeft_naturality f g h).1 z
    rw [tensorProdLeft_maps.1] at hh
    exact hh.symm
  have hin (s : torsionTensor) (t : finsuppTensor) :
      T productCoefficients (f.prodMap g) (includeC s + includeD t) =
        includeC (T torsionCoefficients f s) + includeD (T finsuppCoefficients g t) := by
    have hh := DFunLike.congr_fun (tensorProdLeft_naturality f g h).2 (s, t)
    change T productCoefficients (f.prodMap g)
      ((TopModuleCat.tensorProdLeft ℤ torsionCoefficients finsuppCoefficients
        rightModule).symm (s, t)) =
      (TopModuleCat.tensorProdLeft ℤ torsionCoefficients finsuppCoefficients
        rightModule).symm (T torsionCoefficients f s, T finsuppCoefficients g t) at hh
    rw [(tensorProdLeft_values 0 s t).2,
      (tensorProdLeft_values 0 (T torsionCoefficients f s) (T finsuppCoefficients g t)).2] at hh
    exact hh
  have hb := (quotientTensor_block_values B).1
  have hproj (w : Q productCoefficients) :
      (quotientProjectC B (V productCoefficients (f.prodMap g) w),
        quotientProjectD B (V productCoefficients (f.prodMap g) w)) =
      (V torsionCoefficients f (quotientProjectC B w),
        V finsuppCoefficients g (quotientProjectD B w)) := by
    obtain ⟨z, rfl⟩ := TopModuleCat.cokerπ_surjective (φ productCoefficients) w
    have hC : quotientProjectC B
        (V productCoefficients (f.prodMap g) (q productCoefficients z)) =
        V torsionCoefficients f (quotientProjectC B (q productCoefficients z)) :=
      (congrArg (quotientProjectC B) (hV productCoefficients (f.prodMap g) z)).trans
        ((hb (T productCoefficients (f.prodMap g) z) 0 0).1.trans
          ((congrArg (q torsionCoefficients) (congrArg Prod.fst (hp z))).trans
            ((hV torsionCoefficients f (projectC z)).symm.trans
              (congrArg (V torsionCoefficients f) (hb z 0 0).1.symm))))
    have hD : quotientProjectD B
        (V productCoefficients (f.prodMap g) (q productCoefficients z)) =
        V finsuppCoefficients g (quotientProjectD B (q productCoefficients z)) :=
      (congrArg (quotientProjectD B) (hV productCoefficients (f.prodMap g) z)).trans
        ((hb (T productCoefficients (f.prodMap g) z) 0 0).2.1.trans
          ((congrArg (q finsuppCoefficients) (congrArg Prod.snd (hp z))).trans
            ((hV finsuppCoefficients g (projectD z)).symm.trans
              (congrArg (V finsuppCoefficients g) (hb z 0 0).2.1.symm))))
    exact Prod.ext hC hD
  refine ⟨hV torsionCoefficients f, hV finsuppCoefficients g,
    hV productCoefficients (f.prodMap g), hproj, ?_, ?_⟩
  · intro a b
    obtain ⟨s, rfl⟩ := TopModuleCat.cokerπ_surjective (φ torsionCoefficients) a
    obtain ⟨t, rfl⟩ := TopModuleCat.cokerπ_surjective (φ finsuppCoefficients) b
    have hsum : quotientIncludeC B (q torsionCoefficients s) +
        quotientIncludeD B (q finsuppCoefficients t) =
        q productCoefficients (includeC s + includeD t) :=
      (congrArg₂ (fun a b ↦ a + b) (hb 0 s t).2.2.1 (hb 0 s t).2.2.2).trans
        (map_add (q productCoefficients) (includeC s) (includeD t)).symm
    have hC : q productCoefficients (includeC (T torsionCoefficients f s)) =
        quotientIncludeC B (V torsionCoefficients f (q torsionCoefficients s)) :=
      (hb 0 (T torsionCoefficients f s) (T finsuppCoefficients g t)).2.2.1.symm.trans
        (congrArg (quotientIncludeC B) (hV torsionCoefficients f s).symm)
    have hD : q productCoefficients (includeD (T finsuppCoefficients g t)) =
        quotientIncludeD B (V finsuppCoefficients g (q finsuppCoefficients t)) :=
      (hb 0 (T torsionCoefficients f s) (T finsuppCoefficients g t)).2.2.2.symm.trans
        (congrArg (quotientIncludeD B) (hV finsuppCoefficients g t).symm)
    exact (congrArg (V productCoefficients (f.prodMap g)) hsum).trans
      ((hV productCoefficients (f.prodMap g) (includeC s + includeD t)).trans
        ((congrArg (q productCoefficients) (hin s t)).trans
          ((map_add (q productCoefficients) _ _).trans
            (congrArg₂ (fun a b ↦ a + b) hC hD))))
  · intro n k x y W
    have hC : quotientProjectC B W = q torsionCoefficients (u0 + u1) :=
      (hb (includeC (u0 + u1) + includeD (w n + v n x + v k y)) 0 0).1.trans
        (congrArg (q torsionCoefficients)
          (mixed_projections (u0 + u1) (w n + v n x + v k y)).1)
    have hD : quotientProjectD B W =
        q finsuppCoefficients (w n + v n x + v k y) :=
      (hb (includeC (u0 + u1) + includeD (w n + v n x + v k y)) 0 0).2.1.trans
        (congrArg (q finsuppCoefficients)
          (mixed_projections (u0 + u1) (w n + v n x + v k y)).2)
    exact (hproj W).trans (Prod.ext
      ((congrArg (V torsionCoefficients f) hC).trans
        (hV torsionCoefficients f (u0 + u1)))
      ((congrArg (V finsuppCoefficients g) hD).trans
        (hV finsuppCoefficients g (w n + v n x + v k y))))

/-- Doubling the Finsupp block changes both real controls in the zero and rational quotients. -/
private theorem quotientTensor_scaled_values (n k : ℕ) (hnk : n ≠ k) :
    let B0 : Submodule ℤ ℝ := ⊥
    let BQ : Submodule ℤ ℝ := (Submodule.span ℚ {(1 : ℝ)}).restrictScalars ℤ
    let φ : (B : Submodule ℤ ℝ) → (H : ModuleCat ℤ) →
        TopModuleCat.Hom
          (TopModuleCat.tensorLeftObj ℤ H (TopModuleCat.of ℤ (evenRightSubmodule B)))
          (TopModuleCat.tensorLeftObj ℤ H rightModule) :=
      fun B H ↦ CategoryTheory.ConcreteCategory.ofHom
        (C := TopModuleCat ℤ)
        (X := TopModuleCat.tensorLeftObj ℤ H (TopModuleCat.of ℤ (evenRightSubmodule B)))
        (Y := TopModuleCat.tensorLeftObj ℤ H rightModule)
        (TopModuleCat.tensorMapCLM ℤ (C := H) (D := H)
          (M := TopModuleCat.of ℤ (evenRightSubmodule B)) (N := rightModule)
          (LinearMap.id : H →ₗ[ℤ] H) (evenRightSubmodule B).subtypeL)
    let q := fun (B : Submodule ℤ ℝ) (H : ModuleCat ℤ) ↦
      (TopModuleCat.cokerπ (φ B H)).hom
    let e := fun (B : Submodule ℤ ℝ) ↦
      TopModuleCat.tensorQuotient ℤ productCoefficients rightModule (evenRightSubmodule B)
    let V := fun B : Submodule ℤ ℝ ↦
      (e B).toContinuousLinearMap.comp
        ((TopModuleCat.tensorMapCLM ℤ (C := productCoefficients) (D := productCoefficients)
          (M := TopModuleCat.of ℤ (rightModule ⧸ evenRightSubmodule B))
          (N := TopModuleCat.of ℤ (rightModule ⧸ evenRightSubmodule B))
          ((LinearMap.id : torsionCoefficients →ₗ[ℤ] torsionCoefficients).prodMap
            ((2 : ℤ) • (LinearMap.id : finsuppCoefficients →ₗ[ℤ] finsuppCoefficients)))
          (ContinuousLinearMap.id ℤ (TopModuleCat.of ℤ
            (rightModule ⧸ evenRightSubmodule B)))).comp
          (e B).symm.toContinuousLinearMap)
    let W0 := q B0 productCoefficients
      (includeC (u0 + u1) + includeD (w n + v n 1 + v k 2))
    let WQ := q BQ productCoefficients
      (includeC (u0 + u1) + includeD (w n + v n (Real.sqrt 2) + v k (2 * Real.sqrt 2)))
    (quotientTorsionDetector B0 (quotientProjectC B0 W0),
      quotientIntegerDetector B0 n (quotientProjectD B0 W0),
      quotientRealDetector B0 n (quotientProjectD B0 W0),
      quotientRealDetector B0 k (quotientProjectD B0 W0)) =
        (c0 + c1, (1 : ZMod 2), B0.mkQ 1, B0.mkQ 2) ∧
    (quotientTorsionDetector B0 (quotientProjectC B0 (V B0 W0)),
      quotientIntegerDetector B0 n (quotientProjectD B0 (V B0 W0)),
      quotientRealDetector B0 n (quotientProjectD B0 (V B0 W0)),
      quotientRealDetector B0 k (quotientProjectD B0 (V B0 W0))) =
        (c0 + c1, (0 : ZMod 2), B0.mkQ 2, B0.mkQ 4) ∧
    B0.mkQ 1 ≠ 0 ∧ B0.mkQ 2 ≠ 0 ∧ B0.mkQ 4 ≠ 0 ∧
    B0.mkQ 2 ≠ B0.mkQ 1 ∧ B0.mkQ 4 ≠ B0.mkQ 2 ∧
    V B0 W0 ≠ W0 ∧
    (quotientTorsionDetector BQ (quotientProjectC BQ WQ),
      quotientIntegerDetector BQ n (quotientProjectD BQ WQ),
      quotientRealDetector BQ n (quotientProjectD BQ WQ),
      quotientRealDetector BQ k (quotientProjectD BQ WQ)) =
        (c0 + c1, (1 : ZMod 2), BQ.mkQ (Real.sqrt 2), BQ.mkQ (2 * Real.sqrt 2)) ∧
    (quotientTorsionDetector BQ (quotientProjectC BQ (V BQ WQ)),
      quotientIntegerDetector BQ n (quotientProjectD BQ (V BQ WQ)),
      quotientRealDetector BQ n (quotientProjectD BQ (V BQ WQ)),
      quotientRealDetector BQ k (quotientProjectD BQ (V BQ WQ))) =
        (c0 + c1, (0 : ZMod 2), BQ.mkQ (2 * Real.sqrt 2), BQ.mkQ (4 * Real.sqrt 2)) ∧
    BQ.mkQ (Real.sqrt 2) ≠ 0 ∧ BQ.mkQ (2 * Real.sqrt 2) ≠ 0 ∧
    BQ.mkQ (4 * Real.sqrt 2) ≠ 0 ∧
    BQ.mkQ (2 * Real.sqrt 2) ≠ BQ.mkQ (Real.sqrt 2) ∧
    BQ.mkQ (4 * Real.sqrt 2) ≠ BQ.mkQ (2 * Real.sqrt 2) ∧
    V BQ WQ ≠ WQ := by
  classical
  intro B0 BQ φ q e V W0 WQ
  let l := (LinearMap.id : torsionCoefficients →ₗ[ℤ] torsionCoefficients).prodMap
    ((2 : ℤ) • (LinearMap.id : finsuppCoefficients →ₗ[ℤ] finsuppCoefficients))
  let T := TopModuleCat.tensorMapCLM ℤ (C := productCoefficients) (D := productCoefficients)
    (M := rightModule) (N := rightModule) l (ContinuousLinearMap.id ℤ rightModule)
  have hV (B : Submodule ℤ ℝ) (z : productTensor) :
      V B (q B productCoefficients z) = q B productCoefficients (T z) := by
    let P := evenRightSubmodule B
    let Mbar := TopModuleCat.of ℤ (rightModule ⧸ P)
    let hbar := P.liftQL
      (P.mkQL.comp (ContinuousLinearMap.id ℤ rightModule)) (by
        intro m hm
        change P.mkQ m = 0
        exact (Submodule.Quotient.mk_eq_zero P).mpr hm)
    have hid : hbar = ContinuousLinearMap.id ℤ Mbar := by
      apply ContinuousLinearMap.coe_injective
      apply LinearMap.ext
      intro a
      obtain ⟨m, rfl⟩ := P.mkQ_surjective a
      change P.liftQ (P.mkQL.comp (ContinuousLinearMap.id ℤ rightModule)).toLinearMap
        _ (P.mkQ m) = P.mkQ m
      exact P.liftQ_apply (P.mkQL.comp (ContinuousLinearMap.id ℤ rightModule)).toLinearMap m
    have hm := (quotientTensor_mapped_values B
      (LinearMap.id : torsionCoefficients →ₗ[ℤ] torsionCoefficients)
      ((2 : ℤ) • (LinearMap.id : finsuppCoefficients →ₗ[ℤ] finsuppCoefficients))
      (ContinuousLinearMap.id ℤ rightModule) (by intro m hm; exact hm)).2.2.1 z
    change (e B)
      (TopModuleCat.tensorMapCLM ℤ
        (C := productCoefficients) (D := productCoefficients)
        (M := Mbar) (N := Mbar) l hbar
        ((e B).symm (q B productCoefficients z))) =
      q B productCoefficients (T z) at hm
    rw [hid] at hm
    exact hm
  have hbase (B : Submodule ℤ ℝ) (x y : ℝ) (hx : B.mkQ x ≠ 0) (hy : B.mkQ y ≠ 0) :
      (quotientTorsionDetector B (quotientProjectC B
          (q B productCoefficients (includeC (u0 + u1) + includeD (w n + v n x + v k y)))),
        quotientIntegerDetector B n (quotientProjectD B
          (q B productCoefficients (includeC (u0 + u1) + includeD (w n + v n x + v k y)))),
        quotientRealDetector B n (quotientProjectD B
          (q B productCoefficients (includeC (u0 + u1) + includeD (w n + v n x + v k y)))),
        quotientRealDetector B k (quotientProjectD B
          (q B productCoefficients (includeC (u0 + u1) + includeD (w n + v n x + v k y))))) =
        (c0 + c1, (1 : ZMod 2), B.mkQ x, B.mkQ y) := by
    rcases quotientTensor_mixed_controls B n k hnk x y hx hy with
      ⟨_, _, _, _, _, _, _, _, hp, _, hd, _⟩
    exact (congrArg
      (fun p : TopModuleCat.coker (φ B torsionCoefficients) ×
          TopModuleCat.coker (φ B finsuppCoefficients) ↦
        (quotientTorsionDetector B p.1, quotientIntegerDetector B n p.2,
          quotientRealDetector B n p.2, quotientRealDetector B k p.2)) hp).trans hd
  have hscaled (B : Submodule ℤ ℝ) (x y : ℝ) (hx : B.mkQ x ≠ 0) (hy : B.mkQ y ≠ 0) :
      (quotientTorsionDetector B (quotientProjectC B
          (V B (q B productCoefficients (includeC (u0 + u1) + includeD (w n + v n x + v k y))))),
        quotientIntegerDetector B n (quotientProjectD B
          (V B (q B productCoefficients (includeC (u0 + u1) + includeD (w n + v n x + v k y))))),
        quotientRealDetector B n (quotientProjectD B
          (V B (q B productCoefficients (includeC (u0 + u1) + includeD (w n + v n x + v k y))))),
        quotientRealDetector B k (quotientProjectD B
          (V B (q B productCoefficients (includeC (u0 + u1) + includeD (w n + v n x + v k y)))))) =
        (c0 + c1, (0 : ZMod 2), B.mkQ (2 * x), B.mkQ (2 * y)) := by
    let t := w n + v n x + v k y
    let z := includeC (u0 + u1) + includeD t
    have hx' : x ≠ 0 := by
      intro hz
      exact hx (by rw [hz, map_zero])
    have hy' : y ≠ 0 := by
      intro hz
      exact hy (by rw [hz, map_zero])
    rcases tensorProdLeft_mixed_controls hnk hx' hy' with
      ⟨he, _, _, ht, hi, hrn, hrk, _⟩
    rw [he] at ht hi hrn hrk
    have hp : (projectC (T z), projectD (T z)) = (u0 + u1, (2 : ℤ) • t) := by
      have hm := tensorProdLeft_mapped_mixed
        (LinearMap.id : torsionCoefficients →ₗ[ℤ] torsionCoefficients)
        ((2 : ℤ) • (LinearMap.id : finsuppCoefficients →ₗ[ℤ] finsuppCoefficients))
        (ContinuousLinearMap.id ℤ rightModule) n k x y
      have hCmap : TopModuleCat.tensorMapCLM ℤ
          (C := torsionCoefficients) (D := torsionCoefficients)
          (M := rightModule) (N := rightModule)
          (LinearMap.id : torsionCoefficients →ₗ[ℤ] torsionCoefficients)
          (ContinuousLinearMap.id ℤ rightModule) =
          ContinuousLinearMap.id ℤ torsionTensor :=
        TopModuleCat.tensorMapCLM_id ℤ (C := torsionCoefficients) (M := rightModule)
      have hDmap : TopModuleCat.tensorMapCLM ℤ
          (C := finsuppCoefficients) (D := finsuppCoefficients)
          (M := rightModule) (N := rightModule)
          ((2 : ℤ) • (LinearMap.id : finsuppCoefficients →ₗ[ℤ] finsuppCoefficients))
          (ContinuousLinearMap.id ℤ rightModule) =
          (2 : ℤ) • ContinuousLinearMap.id ℤ finsuppTensor := by
        exact (TopModuleCat.tensorMapCLM_smul_left ℤ
          (C := finsuppCoefficients) (D := finsuppCoefficients)
          (M := rightModule) (N := rightModule) (2 : ℤ)
          (LinearMap.id : finsuppCoefficients →ₗ[ℤ] finsuppCoefficients)
          (ContinuousLinearMap.id ℤ rightModule)).trans
            (congrArg (fun F : finsuppTensor →L[ℤ] finsuppTensor ↦ (2 : ℤ) • F)
              (TopModuleCat.tensorMapCLM_id ℤ
                (C := finsuppCoefficients) (M := rightModule)))
      have he := (tensorProdLeft_values (T z) 0 0).1
      exact Prod.ext
        ((congrArg Prod.fst he).symm.trans
          ((congrArg Prod.fst hm).trans (DFunLike.congr_fun hCmap (u0 + u1))))
        ((congrArg Prod.snd he).symm.trans
          ((congrArg Prod.snd hm).trans (DFunLike.congr_fun hDmap t)))
    have hb := (quotientTensor_block_values B).1 (T z) 0 0
    have hd := (quotientTensor_detector_values B).1
    have hCq : quotientProjectC B (V B (q B productCoefficients z)) =
        q B torsionCoefficients (u0 + u1) :=
      (congrArg (quotientProjectC B) (hV B z)).trans
        (hb.1.trans (congrArg (q B torsionCoefficients) (congrArg Prod.fst hp)))
    have hDq : quotientProjectD B (V B (q B productCoefficients z)) =
        q B finsuppCoefficients ((2 : ℤ) • t) :=
      (congrArg (quotientProjectD B) (hV B z)).trans
        (hb.2.1.trans (congrArg (q B finsuppCoefficients) (congrArg Prod.snd hp)))
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
    · exact (congrArg (quotientTorsionDetector B) hCq).trans
        ((hd (u0 + u1) 0 n).1.trans ht)
    · have hi2 : integerDetector n ((2 : ℤ) • t) = (2 : ℤ) := by
        rw [map_smul, hi]
        norm_num
      have hcast2 : (Int.castAddHom (ZMod 2)).toIntLinearMap (2 : ℤ) =
          (0 : ZMod 2) := by
        change ((2 : ℤ) : ZMod 2) = 0
        exact (ZMod.intCast_zmod_eq_zero_iff_dvd 2 2).mpr (dvd_refl (2 : ℤ))
      exact (congrArg (quotientIntegerDetector B n) hDq).trans
        ((hd 0 ((2 : ℤ) • t) n).2.1.trans
          ((congrArg (Int.castAddHom (ZMod 2)).toIntLinearMap hi2).trans hcast2))
    · exact (congrArg (quotientRealDetector B n) hDq).trans
        ((hd 0 ((2 : ℤ) • t) n).2.2.trans (by
          rw [map_smul, hrn]
          simp only [zsmul_eq_mul, Int.cast_ofNat]))
    · exact (congrArg (quotientRealDetector B k) hDq).trans
        ((hd 0 ((2 : ℤ) • t) k).2.2.trans (by
          rw [map_smul, hrk]
          simp only [zsmul_eq_mul, Int.cast_ofNat]))
  have h0 (a : ℝ) (ha : a ≠ 0) : B0.mkQ a ≠ 0 := by
    intro hz
    have hm : a ∈ B0 := (Submodule.Quotient.mk_eq_zero B0).mp hz
    change a ∈ (⊥ : Submodule ℤ ℝ) at hm
    exact ha ((Submodule.mem_bot ℤ).mp hm)
  have hQ (a : ℚ) (ha : a ≠ 0) : BQ.mkQ ((a : ℝ) * Real.sqrt 2) ≠ 0 := by
    intro hz
    have hh := congrArg
      (Submodule.Quotient.restrictScalarsEquiv ℤ (Submodule.span ℚ {(1 : ℝ)})) hz
    have hh' : (Submodule.span ℚ {(1 : ℝ)}).mkQ (a • Real.sqrt 2) = 0 := by
      simpa only [Submodule.mkQ_apply, Submodule.Quotient.restrictScalarsEquiv_mk,
        map_zero, Rat.smul_def] using hh
    rw [map_smul] at hh'
    exact (smul_ne_zero ha AddCircle.RationalQuotient.mkQ_sqrt_two_ne_zero) hh'
  have hQdiff (a b : ℚ) (hab : a ≠ b) :
      BQ.mkQ ((a : ℝ) * Real.sqrt 2) ≠ BQ.mkQ ((b : ℝ) * Real.sqrt 2) := by
    intro hh
    apply hQ (a - b) (sub_ne_zero.mpr hab)
    rw [Rat.cast_sub, sub_mul, map_sub, hh, sub_self]
  have h01 : B0.mkQ 1 ≠ 0 := h0 1 (by norm_num)
  have h02 : B0.mkQ 2 ≠ 0 := h0 2 (by norm_num)
  have h04 : B0.mkQ 4 ≠ 0 := h0 4 (by norm_num)
  have hQ1 : BQ.mkQ (Real.sqrt 2) ≠ 0 := by simpa using hQ 1 one_ne_zero
  have hQ2 : BQ.mkQ (2 * Real.sqrt 2) ≠ 0 := by simpa using hQ 2 (by norm_num)
  have hQ4 : BQ.mkQ (4 * Real.sqrt 2) ≠ 0 := by simpa using hQ 4 (by norm_num)
  have hinit0 := hbase B0 1 2 h01 h02
  have hscale0 := hscaled B0 1 2 h01 h02
  have hinitQ := hbase BQ (Real.sqrt 2) (2 * Real.sqrt 2) hQ1 hQ2
  have hscaleQ := hscaled BQ (Real.sqrt 2) (2 * Real.sqrt 2) hQ1 hQ2
  have hneq0 : V B0 W0 ≠ W0 := by
    intro hh
    have hv := congrArg (fun p ↦ p.2.1) hscale0
    have hw := congrArg (fun p ↦ p.2.1) hinit0
    rw [hh] at hv
    exact (zero_ne_one : (0 : ZMod 2) ≠ 1) (hv.symm.trans hw)
  have hneqQ : V BQ WQ ≠ WQ := by
    intro hh
    have hv := congrArg (fun p ↦ p.2.1) hscaleQ
    have hw := congrArg (fun p ↦ p.2.1) hinitQ
    rw [hh] at hv
    exact (zero_ne_one : (0 : ZMod 2) ≠ 1) (hv.symm.trans hw)
  refine ⟨hinit0, ?_, h01, h02, h04, ?_, ?_, hneq0, hinitQ, ?_,
    hQ1, hQ2, hQ4, ?_, ?_, hneqQ⟩
  · simpa only [mul_one, show (2 : ℝ) * 2 = 4 by norm_num] using hscale0
  · intro hh
    have hz := (map_sub B0.mkQ (2 : ℝ) 1).trans (sub_eq_zero.mpr hh)
    rw [show (2 : ℝ) - 1 = 1 by norm_num] at hz
    exact h01 hz
  · intro hh
    have hz := (map_sub B0.mkQ (4 : ℝ) 2).trans (sub_eq_zero.mpr hh)
    rw [show (4 : ℝ) - 2 = 2 by norm_num] at hz
    exact h02 hz
  · simpa only [show (2 : ℝ) * (2 * Real.sqrt 2) = 4 * Real.sqrt 2 by ring] using hscaleQ
  · simpa only [Rat.cast_ofNat, Rat.cast_one, one_mul] using hQdiff 2 1 (by norm_num)
  · simpa only [Rat.cast_ofNat] using hQdiff 4 2 (by norm_num)

/-- The rational right submodule is not closed and the three irrational classes survive. -/
private theorem quotientTensor_nonclosed :
    let BQ : Submodule ℤ ℝ := (Submodule.span ℚ {(1 : ℝ)}).restrictScalars ℤ
    ¬ IsClosed (evenRightSubmodule BQ : Set rightModule) ∧
    BQ.mkQ (Real.sqrt 2) ≠ 0 ∧ BQ.mkQ (2 * Real.sqrt 2) ≠ 0 ∧
    BQ.mkQ (4 * Real.sqrt 2) ≠ 0 := by
  intro BQ
  rcases quotientTensor_scaled_values 0 1 (by decide) with
    ⟨_, _, _, _, _, _, _, _, _, _, h1, h2, h4, _⟩
  refine ⟨?_, h1, h2, h4⟩
  intro hc
  have hpre := hc.preimage
    (continuous_const.prodMk continuous_id : Continuous (fun x : ℝ ↦ ((0, x) : rightModule)))
  have hset : (fun x : ℝ ↦ ((0, x) : rightModule)) ⁻¹'
      (evenRightSubmodule BQ : Set rightModule) = (BQ : Set ℝ) := by
    ext x
    exact and_iff_right (Submodule.zero_mem (Submodule.span ℤ {(2 : ℤ)}))
  rw [hset] at hpre
  have hrat : Set.range ((↑) : ℚ → ℝ) ⊆ (BQ : Set ℝ) := by
    rintro _ ⟨a, rfl⟩
    exact Submodule.mem_span_singleton.mpr ⟨a, by simp only [Rat.smul_def, mul_one]⟩
  have hclosure := closure_minimal hrat hpre
  rw [Rat.denseRange_cast.closure_range] at hclosure
  apply h1
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact hclosure (Set.mem_univ _)

end CoefficientTensorProdExamples
