/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicDirectLimits.Topology.TensorHom
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
public import Mathlib.Topology.Instances.Int

/-!
# Integer-pair bilinear tensor maps

Take algebraic coefficients `C = ℤ × ℤ`, topological right factor `M = ℤ × ℤ`,
and target `N = ℤ`. A linear combination of the canonical continuous projections
constructs the dot pairing. Its tensor lift and the inverse Hom equivalence give
the same outgoing map, and the forward Hom equivalence recovers the pairing.

The first pure tensor has value `1`; doubling the right factor by the existing
`TopModuleCat.tensorMapCLM` gives value `2`. The cross tensor lies in the dot map's
kernel but is detected by a second-projection pairing. Restricting the dot map to
the first coefficient gives the first projection, whose kernel is the second axis.
Zero coefficient and right-factor modules, and rank-one coefficients, illustrate
boundaries separately from this nonzero example.

## Implementation notes

Only the tensor generator and tensor map from
`AlgebraicDirectLimits.Topology.TensorProduct` are used for tensor constructions.
No continuous tensor-coordinate equivalence is used.

## References

The continuous bilinear construction is from
`AlgebraicDirectLimits.Topology.TensorHom`, by Formal Frontier Agents, using the
project's earlier coinduced and one-sided tensor modules and Mathlib's universal
property by Kenny Lau and Mario Carneiro. Mathlib's product linear maps are due to
Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov and Eric Wieser; its
continuous product projections are due to Jan-David Salchow, Sébastien Gouëzel,
Jean Lo, Yury Kudryashov, Frédéric Dupuis and Heather Macbeth. The scalar-multiple
linear-map API is Mathlib's `Algebra.Module.LinearMap.End`.
-/

@[expose] public section

open scoped TensorProduct

universe uR uC uM uN

namespace TensorHomExamples

/-- The algebraic rank-two integer coefficient module. -/
abbrev integerPairCoefficients : ModuleCat ℤ := ModuleCat.of ℤ (ℤ × ℤ)

/-- Integer pairs with their product topology, as a topological integer module. -/
abbrev integerPairModule : TopModuleCat ℤ := TopModuleCat.of ℤ (ℤ × ℤ)

/-- The integers with their usual discrete topology. -/
abbrev integerModule : TopModuleCat ℤ := TopModuleCat.of ℤ ℤ

/-- The dot pairing, as an algebraic linear family of continuous linear maps. -/
noncomputable def integerDot :
    integerPairCoefficients →ₗ[ℤ] (integerPairModule →L[ℤ] integerModule) :=
  (LinearMap.fst ℤ ℤ ℤ).smulRight (ContinuousLinearMap.fst ℤ ℤ ℤ) +
    (LinearMap.snd ℤ ℤ ℤ).smulRight (ContinuousLinearMap.snd ℤ ℤ ℤ)

/-- The dot pairing has the usual two-coordinate formula. -/
theorem integerDot_apply (c : integerPairCoefficients) (m : integerPairModule) :
    integerDot c m = c.1 * m.1 + c.2 * m.2 := by
  simp [integerDot, LinearMap.smulRight_apply]

/-- The canonical continuous tensor lift of the dot pairing. -/
noncomputable def integerDotTensor :
    TopModuleCat.tensorLeftObj ℤ integerPairCoefficients integerPairModule →L[ℤ]
      integerModule :=
  TopModuleCat.tensorLiftCLM ℤ integerDot

/-- Construct the same outgoing map using the inverse Hom equivalence. -/
noncomputable def integerDotTensorViaEquiv :
    TopModuleCat.tensorLeftObj ℤ integerPairCoefficients integerPairModule →L[ℤ]
      integerModule :=
  (TopModuleCat.tensorHomLinearEquiv ℤ integerPairCoefficients integerPairModule
    integerModule).symm integerDot

/-- The inverse-equivalence construction agrees with the canonical lift. -/
theorem integerDotTensorViaEquiv_eq : integerDotTensorViaEquiv = integerDotTensor := by
  exact TopModuleCat.tensorHomLinearEquiv_symm_apply ℤ integerDot

/-- The outgoing dot map evaluates pure tensors by the dot pairing. -/
theorem integerDotTensor_tmul (c : integerPairCoefficients) (m : integerPairModule) :
    integerDotTensor (c ⊗ₜ[ℤ] m) = c.1 * m.1 + c.2 * m.2 := by
  exact (TopModuleCat.tensorLiftCLM_tmul ℤ integerDot c m).trans
    (integerDot_apply c m)

/-- The forward Hom equivalence recovers the continuous dot family. -/
theorem integerDotTensor_curry :
    TopModuleCat.tensorHomLinearEquiv ℤ integerPairCoefficients integerPairModule
      integerModule integerDotTensor = integerDot := by
  rw [TopModuleCat.tensorHomLinearEquiv_apply]
  exact TopModuleCat.tensorCurry_tensorLiftCLM ℤ integerDot

/-- The first coefficient restriction is the first continuous projection. -/
theorem integerDotTensor_curry_first :
    TopModuleCat.tensorHomLinearEquiv ℤ integerPairCoefficients integerPairModule
      integerModule integerDotTensor (1, 0) = ContinuousLinearMap.fst ℤ ℤ ℤ := by
  rw [integerDotTensor_curry]
  apply ContinuousLinearMap.ext
  intro m
  simpa using integerDot_apply ((1, 0) : integerPairCoefficients) m

/-- The first coefficient restriction has the second axis as its kernel. -/
theorem integerDotTensor_curry_first_mem_ker (m : integerPairModule) :
    m ∈ LinearMap.ker
      ((TopModuleCat.tensorHomLinearEquiv ℤ integerPairCoefficients integerPairModule
        integerModule integerDotTensor (1, 0)).toLinearMap) ↔ m.1 = 0 := by
  rw [integerDotTensor_curry_first]
  rfl

/-- The tensor of the first coefficient vector and first right-factor vector. -/
noncomputable def integerFirstTensor :
    TopModuleCat.tensorLeftObj ℤ integerPairCoefficients integerPairModule :=
  TopModuleCat.tensorGenerator ℤ integerPairCoefficients integerPairModule (1, 0) (1, 0)

/-- The dot map detects the first tensor with value `1`. -/
theorem integerDotTensor_first : integerDotTensor integerFirstTensor = 1 := by
  calc
    integerDotTensor integerFirstTensor =
        integerDot ((1, 0) : integerPairCoefficients) ((1, 0) : integerPairModule) :=
      TopModuleCat.tensorLiftCLM_tensorGenerator_apply ℤ integerDot _ _
    _ = 1 := (integerDot_apply ((1, 0) : integerPairCoefficients)
      ((1, 0) : integerPairModule)).trans (by simp)

/-- The first tensor is nonzero, as detected by its outgoing dot value. -/
theorem integerFirstTensor_ne_zero : integerFirstTensor ≠ 0 := by
  intro h
  have hv := integerDotTensor_first
  rw [h, map_zero] at hv
  exact (zero_ne_one : (0 : ℤ) ≠ 1) hv

/-- Doubling on the right-factor module is a nonidentity continuous linear map. -/
noncomputable def integerPairDoubling : integerPairModule →L[ℤ] integerPairModule :=
  2 • ContinuousLinearMap.id ℤ integerPairModule

/-- The existing two-factor tensor map with left identity and right doubling. -/
noncomputable def integerTensorDoubling :
    TopModuleCat.tensorLeftObj ℤ integerPairCoefficients integerPairModule →L[ℤ]
      TopModuleCat.tensorLeftObj ℤ integerPairCoefficients integerPairModule :=
  TopModuleCat.tensorMapCLM ℤ
    (LinearMap.id : integerPairCoefficients →ₗ[ℤ] integerPairCoefficients)
    integerPairDoubling

/-- The dot value becomes `2` after doubling the first right-factor vector. -/
theorem integerDotTensor_doubled_first :
    integerDotTensor (integerTensorDoubling integerFirstTensor) = 2 := by
  calc
    integerDotTensor (integerTensorDoubling integerFirstTensor) =
        integerDotTensor
          (TopModuleCat.tensorGenerator ℤ integerPairCoefficients integerPairModule
            ((1, 0) : integerPairCoefficients)
            (integerPairDoubling ((1, 0) : integerPairModule))) :=
      congrArg integerDotTensor
        (TopModuleCat.tensorMapCLM_tensorGenerator_apply ℤ
          (LinearMap.id : integerPairCoefficients →ₗ[ℤ] integerPairCoefficients)
          integerPairDoubling ((1, 0) : integerPairCoefficients) ((1, 0) : integerPairModule))
    _ = integerDot ((1, 0) : integerPairCoefficients)
        (integerPairDoubling ((1, 0) : integerPairModule)) :=
      TopModuleCat.tensorLiftCLM_tensorGenerator_apply ℤ integerDot _ _
    _ = 2 := (integerDot_apply ((1, 0) : integerPairCoefficients)
      (integerPairDoubling ((1, 0) : integerPairModule))).trans
        (by simp [integerPairDoubling])

/-- Doubling moves the first tensor, as detected by its dot value. -/
theorem integerTensorDoubling_first_ne :
    integerTensorDoubling integerFirstTensor ≠ integerFirstTensor := by
  intro h
  have hv := integerDotTensor_doubled_first
  rw [h, integerDotTensor_first] at hv
  exact (by decide : (1 : ℤ) ≠ 2) hv

/-- Precomposing the outgoing dot map by tensor doubling doubles the whole map. -/
theorem integerDotTensor_comp_doubling :
    integerDotTensor.comp integerTensorDoubling = 2 • integerDotTensor := by
  apply TopModuleCat.tensorLeft_ext ℤ
  intro c m
  -- Evaluate composition first, then use additivity in the right factor.
  calc
    _ = integerDotTensor (c ⊗ₜ[ℤ] integerPairDoubling m) :=
      (ContinuousLinearMap.comp_apply integerDotTensor integerTensorDoubling
        (show TopModuleCat.tensorLeftObj ℤ integerPairCoefficients integerPairModule from
          c ⊗ₜ[ℤ] m)).trans
            (congrArg integerDotTensor (TopModuleCat.tensorMapCLM_tmul ℤ
              (LinearMap.id : integerPairCoefficients →ₗ[ℤ] integerPairCoefficients)
              integerPairDoubling c m))
    _ = integerDotTensor (c ⊗ₜ[ℤ] (m + m)) := by
      apply congrArg (fun n : integerPairModule ↦ integerDotTensor (c ⊗ₜ[ℤ] n))
      simp only [integerPairDoubling, two_smul]
      exact add_apply (ContinuousLinearMap.id ℤ integerPairModule)
        (ContinuousLinearMap.id ℤ integerPairModule) m
    _ = integerDotTensor (c ⊗ₜ[ℤ] m) + integerDotTensor (c ⊗ₜ[ℤ] m) :=
      (congrArg integerDotTensor (TensorProduct.tmul_add c m m)).trans
        (integerDotTensor.map_add _ _)
    _ = _ := by
      simpa only [two_smul] using
        (add_apply integerDotTensor integerDotTensor
          (show TopModuleCat.tensorLeftObj ℤ integerPairCoefficients integerPairModule from
            c ⊗ₜ[ℤ] m)).symm

/-- The first coefficient paired with the second right-factor projection. -/
noncomputable def integerSecondProjection :
    integerPairCoefficients →ₗ[ℤ] (integerPairModule →L[ℤ] integerModule) :=
  (LinearMap.fst ℤ ℤ ℤ).smulRight (ContinuousLinearMap.snd ℤ ℤ ℤ)

/-- The outgoing continuous tensor map detecting the cross tensor. -/
noncomputable def integerSecondProjectionTensor :
    TopModuleCat.tensorLeftObj ℤ integerPairCoefficients integerPairModule →L[ℤ]
      integerModule :=
  TopModuleCat.tensorLiftCLM ℤ integerSecondProjection

/-- The tensor of the first coefficient vector and the second right-factor vector. -/
noncomputable def integerCrossTensor :
    TopModuleCat.tensorLeftObj ℤ integerPairCoefficients integerPairModule :=
  TopModuleCat.tensorGenerator ℤ integerPairCoefficients integerPairModule (1, 0) (0, 1)

/-- The dot pairing vanishes on the cross tensor. -/
theorem integerDotTensor_cross : integerDotTensor integerCrossTensor = 0 := by
  calc
    integerDotTensor integerCrossTensor =
        integerDot ((1, 0) : integerPairCoefficients) ((0, 1) : integerPairModule) :=
      TopModuleCat.tensorLiftCLM_tensorGenerator_apply ℤ integerDot _ _
    _ = 0 := (integerDot_apply ((1, 0) : integerPairCoefficients)
      ((0, 1) : integerPairModule)).trans (by simp)

/-- The second-projection pairing detects the cross tensor with value `1`. -/
theorem integerSecondProjectionTensor_cross :
    integerSecondProjectionTensor integerCrossTensor = 1 := by
  calc
    integerSecondProjectionTensor integerCrossTensor =
        integerSecondProjection ((1, 0) : integerPairCoefficients)
          ((0, 1) : integerPairModule) :=
      TopModuleCat.tensorLiftCLM_tensorGenerator_apply ℤ integerSecondProjection _ _
    _ = 1 := by simp [integerSecondProjection, LinearMap.smulRight_apply]

/-- The cross tensor is nonzero despite its zero dot value. -/
theorem integerCrossTensor_ne_zero : integerCrossTensor ≠ 0 := by
  intro h
  have hv := integerSecondProjectionTensor_cross
  rw [h, map_zero] at hv
  exact (zero_ne_one : (0 : ℤ) ≠ 1) hv

/-- The dot tensor map has a nonzero vector in its kernel. -/
theorem integerCrossTensor_mem_ker :
    integerCrossTensor ∈ LinearMap.ker integerDotTensor.toLinearMap := by
  exact integerDotTensor_cross

/-- The canonical dot tensor map is the unique continuous map with the dot values. -/
theorem existsUnique_integerDotTensor :
    ∃! f : TopModuleCat.tensorLeftObj ℤ integerPairCoefficients integerPairModule →L[ℤ]
      integerModule, ∀ c m, f (c ⊗ₜ[ℤ] m) = integerDot c m :=
  TopModuleCat.existsUnique_tensorLiftCLM ℤ integerDot

section Boundaries

variable (R : Type uR) [CommRing R] [TopologicalSpace R]

/-- With zero coefficients, every continuous bilinear family lifts to the zero map. -/
theorem zeroCoefficients_tensorLiftCLM (M : TopModuleCat.{uM} R)
    (N : TopModuleCat.{uN} R)
    (b : ModuleCat.of R (Fin 0 → R) →ₗ[R] (M →L[R] N)) :
    TopModuleCat.tensorLiftCLM R b = 0 := by
  apply TopModuleCat.tensorLeft_ext R
  intro c m
  have hc : c = (0 : ModuleCat.of R (Fin 0 → R)) := by
    funext i
    exact Fin.elim0 i
  rw [TopModuleCat.tensorLiftCLM_tmul, hc, map_zero]
  rfl

/-- With a zero right-factor module, every continuous bilinear family lifts to zero. -/
theorem zeroRightFactor_tensorLiftCLM (C : ModuleCat.{uC} R) (N : TopModuleCat.{uN} R)
    (b : C →ₗ[R]
      (((TopModuleCat.indiscrete R).obj (ModuleCat.of R (Fin 0 → R))) →L[R] N)) :
    TopModuleCat.tensorLiftCLM R b = 0 := by
  apply TopModuleCat.tensorLeft_ext R
  intro c m
  have hm : m = (0 : (TopModuleCat.indiscrete R).obj (ModuleCat.of R (Fin 0 → R))) := by
    funext i
    exact Fin.elim0 i
  rw [TopModuleCat.tensorLiftCLM_tmul, hm, map_zero]
  rfl

/-- A continuous linear map supplies a rank-one coefficient family by scalar multiplication. -/
noncomputable def rankOnePairing {M : TopModuleCat.{uM} R} {N : TopModuleCat.{uN} R}
    (g : M →L[R] N) : ModuleCat.of R R →ₗ[R] (M →L[R] N) :=
  (LinearMap.id : R →ₗ[R] R).smulRight g

private theorem rankOnePairing_apply {M : TopModuleCat.{uM} R}
    {N : TopModuleCat.{uN} R} (g : M →L[R] N) (r : R) :
    rankOnePairing R g r = r • g :=
  LinearMap.smulRight_apply _ _ _

/-- The rank-one lift sends `r ⊗ m` to `r • g m`. -/
theorem rankOnePairing_tensorLiftCLM_tmul {M : TopModuleCat.{uM} R}
    {N : TopModuleCat.{uN} R} (g : M →L[R] N) (r : R) (m : M) :
    TopModuleCat.tensorLiftCLM R (rankOnePairing R g) (r ⊗ₜ[R] m) = r • g m := by
  rw [TopModuleCat.tensorLiftCLM_tmul, rankOnePairing_apply, smul_apply]

/-- Restricting the rank-one lift to the coefficient `1` recovers the original map. -/
theorem rankOnePairing_tensorLiftCLM_comp_generator {M : TopModuleCat.{uM} R}
    {N : TopModuleCat.{uN} R} (g : M →L[R] N) :
    (TopModuleCat.tensorLiftCLM R (rankOnePairing R g)).comp
      (TopModuleCat.tensorGenerator R (ModuleCat.of R R) M 1) = g := by
  rw [TopModuleCat.tensorLiftCLM_comp_tensorGenerator, rankOnePairing_apply, one_smul]

end Boundaries

end TensorHomExamples
