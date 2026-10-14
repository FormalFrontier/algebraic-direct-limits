/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicDirectLimitsExamples.TensorHom
public import AlgebraicDirectLimitsExamples.ProjectiveTensorSeparation

/-!
# Naturality of continuous tensor lifts and curried maps

Coefficient restrictions and nonidentity continuous right maps act on tensor
lifts. Coordinate readouts and doubling of targets act on curried maps. Examples
use integer dot pairings, countably infinite integer coefficients with the usual
reals, and a nonfree ideal over the product ring of integers.

## Implementation notes

The coefficient objects are algebraic. All outgoing and right-variable maps are
bundled continuous linear maps. Infinite coordinates take values in an ordinary
product. Only the canonical one-sided tensor, lift, curry and composition APIs
are used.

## References

These examples use the tensor and continuous bilinear APIs by Formal Frontier
Agents, following the continuous group cohomology development including Beacon,
and the arbitrary-coordinate and ideal examples following Lantern. Mathlib's
tensor universal property is by Kenny Lau and Mario Carneiro, its topological
modules by Richard Hill and Andrew Yang, its linear/product/Finsupp and basis
APIs by Johannes Hölzl, Simon Hudon, Patrick Massot, Mario Carneiro, Kim Morrison,
Eric Wieser, Alexander Bentkamp and Jakob von Raumer, and its continuous linear
maps by Jan-David Salchow, Sébastien Gouëzel, Jean Lo, Yury Kudryashov, Frédéric
Dupuis and Heather Macbeth. The imported example modules retain their complete
source-specific mathematical credits and notices.
-/

@[expose] public section

open scoped TensorProduct
open TensorHomExamples ProjectiveTensorSeparationExamples

namespace TensorHomNaturalityExamples

/-- Regular algebraic integer coefficients for axis restrictions. -/
abbrev regularIntegerCoefficients : ModuleCat ℤ := ModuleCat.of ℤ ℤ

/-- Inclusion of regular coefficients into the first integer axis. -/
def integerFirstInclusion : regularIntegerCoefficients →ₗ[ℤ] integerPairCoefficients :=
  LinearMap.inl ℤ ℤ ℤ

/-- Inclusion of regular coefficients into the second integer axis. -/
def integerSecondInclusion : regularIntegerCoefficients →ₗ[ℤ] integerPairCoefficients :=
  LinearMap.inr ℤ ℤ ℤ

/-- Doubling of the integer target of the dot pairing. -/
noncomputable def integerPostDoubling : integerModule →L[ℤ] integerModule :=
  (2 : ℤ) • ContinuousLinearMap.id ℤ integerModule

/-- The ordinary product of real integer modules, with product topology. -/
abbrev coordinateModule : TopModuleCat ℤ := TopModuleCat.of ℤ (ℕ → realModule)

/-- A regular coefficient is sent to its multiple of one infinite basis vector. -/
noncomputable def infiniteBasisInclusion (n : ℕ) :
    regularIntegerCoefficients →ₗ[ℤ] infiniteCoefficients :=
  (LinearMap.id : regularIntegerCoefficients →ₗ[ℤ] ℤ).smulRight (integerBasisVector n)

/-- Doubling of the usual real integer module. -/
noncomputable def realDoubling : realModule →L[ℤ] realModule :=
  (2 : ℤ) • ContinuousLinearMap.id ℤ realModule

/-- Reading one coordinate of an ordinary product is continuous and linear. -/
def coordinateReadout (i : ℕ) : coordinateModule →L[ℤ] realModule :=
  ContinuousLinearMap.proj (R := ℤ) (φ := fun _ : ℕ ↦ realModule) i

/-- Doubling of the regular module over the componentwise integer product ring. -/
noncomputable def productDoubling : productModule →L[productRing] productModule :=
  (2 : productRing) • ContinuousLinearMap.id productRing productModule

/-- The ideal inclusion paired with the continuous regular right identity. -/
noncomputable def firstAxisPairing :
    firstAxisCoefficients →ₗ[productRing] (productModule →L[productRing] productModule) :=
  firstAxisIdeal.subtype.smulRight (ContinuousLinearMap.id productRing productModule)

/-- The two axis restrictions commute with lift and nonidentity right doubling. -/
theorem integer_lift_restrictions
    (b : integerPairCoefficients →ₗ[ℤ] (integerPairModule →L[ℤ] integerModule)) :
    TopModuleCat.tensorLiftCLM ℤ
        ((ContinuousLinearMap.lcomp integerModule integerPairDoubling).comp
          (b.comp integerFirstInclusion)) =
      (TopModuleCat.tensorLiftCLM ℤ b).comp
        (TopModuleCat.tensorMapCLM ℤ integerFirstInclusion integerPairDoubling) ∧
    TopModuleCat.tensorLiftCLM ℤ
        ((ContinuousLinearMap.lcomp integerModule integerPairDoubling).comp
          (b.comp integerSecondInclusion)) =
      (TopModuleCat.tensorLiftCLM ℤ b).comp
        (TopModuleCat.tensorMapCLM ℤ integerSecondInclusion integerPairDoubling) := by
  constructor
  · exact TopModuleCat.tensorLiftCLM_comp_tensorMapCLM ℤ
      (C := integerPairCoefficients) (D := regularIntegerCoefficients)
      (M := integerPairModule) (N := integerModule) (P := integerPairModule)
      b integerFirstInclusion integerPairDoubling
  · exact TopModuleCat.tensorLiftCLM_comp_tensorMapCLM ℤ
      (C := integerPairCoefficients) (D := regularIntegerCoefficients)
      (M := integerPairModule) (N := integerModule) (P := integerPairModule)
      b integerSecondInclusion integerPairDoubling

/-- Target doubling postcomposes the entire curried family of any outgoing map. -/
theorem integer_curry_postdoubling
    (f : TopModuleCat.tensorLeftObj ℤ integerPairCoefficients integerPairModule →L[ℤ]
      integerModule) :
    TopModuleCat.tensorCurry ℤ (integerPostDoubling.comp f) =
      ((ContinuousLinearMap.llcomp ℤ integerPairModule integerModule integerModule).flip
        integerPostDoubling).comp (TopModuleCat.tensorCurry ℤ f) := by
  exact TopModuleCat.tensorCurry_comp ℤ (C := integerPairCoefficients)
    (M := integerPairModule) (N := integerModule) (P := integerModule)
    f integerPostDoubling

/-- Axis restrictions read different coordinates on variable mixed tensors;
target doubling changes the variable dot value. -/
theorem integer_restrictions_values (r s : ℤ) (m n : integerPairModule)
    (c : integerPairCoefficients) :
    TopModuleCat.tensorLiftCLM ℤ
        ((ContinuousLinearMap.lcomp integerModule integerPairDoubling).comp
          (integerDot.comp integerFirstInclusion))
        (r ⊗ₜ[ℤ] m + s ⊗ₜ[ℤ] n) = r * (2 * m.1) + s * (2 * n.1) ∧
    TopModuleCat.tensorLiftCLM ℤ
        ((ContinuousLinearMap.lcomp integerModule integerPairDoubling).comp
          (integerDot.comp integerSecondInclusion))
        (r ⊗ₜ[ℤ] m + s ⊗ₜ[ℤ] n) = r * (2 * m.2) + s * (2 * n.2) ∧
    TopModuleCat.tensorCurry ℤ (integerPostDoubling.comp integerDotTensor) c m =
      2 * (c.1 * m.1 + c.2 * m.2) := by
  let b₁ : regularIntegerCoefficients →ₗ[ℤ] (integerPairModule →L[ℤ] integerModule) :=
    (ContinuousLinearMap.lcomp integerModule integerPairDoubling).comp
      (integerDot.comp integerFirstInclusion)
  let b₂ : regularIntegerCoefficients →ₗ[ℤ] (integerPairModule →L[ℤ] integerModule) :=
    (ContinuousLinearMap.lcomp integerModule integerPairDoubling).comp
      (integerDot.comp integerSecondInclusion)
  constructor
  · calc
      _ = integerDot (integerFirstInclusion r) (integerPairDoubling m) +
          integerDot (integerFirstInclusion s) (integerPairDoubling n) :=
        ((TopModuleCat.tensorLiftCLM ℤ (C := regularIntegerCoefficients)
          (M := integerPairModule) (N := integerModule) b₁).map_add
          (show TopModuleCat.tensorLeftObj ℤ regularIntegerCoefficients integerPairModule from
            r ⊗ₜ[ℤ] m)
          (show TopModuleCat.tensorLeftObj ℤ regularIntegerCoefficients integerPairModule from
            s ⊗ₜ[ℤ] n)).trans
          (congrArg₂ (fun x y : integerModule ↦ x + y)
            (TopModuleCat.tensorLiftCLM_tmul ℤ (C := regularIntegerCoefficients)
              (M := integerPairModule) (N := integerModule) b₁ r m)
            (TopModuleCat.tensorLiftCLM_tmul ℤ (C := regularIntegerCoefficients)
              (M := integerPairModule) (N := integerModule) b₁ s n))
      _ = _ := congrArg₂ (fun x y : ℤ ↦ x + y)
        ((integerDot_apply (integerFirstInclusion r) (integerPairDoubling m)).trans
          (by simp [integerFirstInclusion, integerPairDoubling]))
        ((integerDot_apply (integerFirstInclusion s) (integerPairDoubling n)).trans
          (by simp [integerFirstInclusion, integerPairDoubling]))
  · constructor
    · calc
        _ = integerDot (integerSecondInclusion r) (integerPairDoubling m) +
            integerDot (integerSecondInclusion s) (integerPairDoubling n) :=
          ((TopModuleCat.tensorLiftCLM ℤ (C := regularIntegerCoefficients)
            (M := integerPairModule) (N := integerModule) b₂).map_add
            (show TopModuleCat.tensorLeftObj ℤ regularIntegerCoefficients integerPairModule from
              r ⊗ₜ[ℤ] m)
            (show TopModuleCat.tensorLeftObj ℤ regularIntegerCoefficients integerPairModule from
              s ⊗ₜ[ℤ] n)).trans
            (congrArg₂ (fun x y : integerModule ↦ x + y)
              (TopModuleCat.tensorLiftCLM_tmul ℤ (C := regularIntegerCoefficients)
                (M := integerPairModule) (N := integerModule) b₂ r m)
              (TopModuleCat.tensorLiftCLM_tmul ℤ (C := regularIntegerCoefficients)
                (M := integerPairModule) (N := integerModule) b₂ s n))
        _ = _ := congrArg₂ (fun x y : ℤ ↦ x + y)
          ((integerDot_apply (integerSecondInclusion r) (integerPairDoubling m)).trans
            (by simp [integerSecondInclusion, integerPairDoubling]))
          ((integerDot_apply (integerSecondInclusion s) (integerPairDoubling n)).trans
            (by simp [integerSecondInclusion, integerPairDoubling]))
    · calc
        _ = integerPostDoubling (integerDotTensor (c ⊗ₜ[ℤ] m)) :=
          (TopModuleCat.tensorCurry_apply_apply ℤ (C := integerPairCoefficients)
            (M := integerPairModule) (N := integerModule)
            (integerPostDoubling.comp integerDotTensor) c m).trans
            (ContinuousLinearMap.comp_apply integerPostDoubling integerDotTensor
              (show TopModuleCat.tensorLeftObj ℤ integerPairCoefficients integerPairModule from
                c ⊗ₜ[ℤ] m))
        _ = integerPostDoubling (c.1 * m.1 + c.2 * m.2) :=
          congrArg integerPostDoubling (integerDotTensor_tmul c m)
        _ = _ := by
          simp only [integerPostDoubling, smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]

/-- Basis-vector restrictions commute with lift and real right doubling. -/
theorem infinite_lift_restriction
    (b : infiniteCoefficients →ₗ[ℤ] (realModule →L[ℤ] coordinateModule)) (k : ℕ) :
    TopModuleCat.tensorLiftCLM ℤ
        ((ContinuousLinearMap.lcomp coordinateModule realDoubling).comp
          (b.comp (infiniteBasisInclusion k))) =
      (TopModuleCat.tensorLiftCLM ℤ b).comp
        (TopModuleCat.tensorMapCLM ℤ (infiniteBasisInclusion k) realDoubling) := by
  exact TopModuleCat.tensorLiftCLM_comp_tensorMapCLM ℤ
    (C := infiniteCoefficients) (D := regularIntegerCoefficients)
    (M := realModule) (N := coordinateModule) (P := realModule)
    b (infiniteBasisInclusion k) realDoubling

/-- Reading a product coordinate postcomposes any outgoing curried family. -/
theorem infinite_curry_readout
    (f : infiniteTensor →L[ℤ] coordinateModule) (i : ℕ) :
    TopModuleCat.tensorCurry ℤ ((coordinateReadout i).comp f) =
      ((ContinuousLinearMap.llcomp ℤ realModule coordinateModule realModule).flip
        (coordinateReadout i)).comp (TopModuleCat.tensorCurry ℤ f) := by
  exact TopModuleCat.tensorCurry_comp ℤ (C := infiniteCoefficients)
    (M := realModule) (N := coordinateModule) (P := realModule) f (coordinateReadout i)

/-- The coordinate family retains basis position on variable mixed inputs,
and the postcomposed curry reads each arbitrary coefficient coordinate. -/
theorem infinite_restriction_readout_values (k i : ℕ) (r s : ℤ) (m n : realModule)
    (c : infiniteCoefficients) :
    TopModuleCat.tensorLiftCLM ℤ
        ((ContinuousLinearMap.lcomp coordinateModule realDoubling).comp
          ((TopModuleCat.tensorCurry ℤ infiniteCoordinates).comp (infiniteBasisInclusion k)))
        (r ⊗ₜ[ℤ] m + s ⊗ₜ[ℤ] n) i =
      (if k = i then r • ((2 : ℤ) • m) + s • ((2 : ℤ) • n) else 0) ∧
    ((coordinateReadout i).comp infiniteCoordinates)
        (integerBasisVector 0 ⊗ₜ[ℤ] m + integerBasisVector 1 ⊗ₜ[ℤ] n) =
      (if (0 : ℕ) = i then m else 0) + (if (1 : ℕ) = i then n else 0) ∧
    TopModuleCat.tensorCurry ℤ ((coordinateReadout i).comp infiniteCoordinates) c m =
      infiniteBasis.repr c i • m := by
  let q : infiniteCoefficients →ₗ[ℤ] (realModule →L[ℤ] coordinateModule) :=
    TopModuleCat.tensorCurry ℤ (C := infiniteCoefficients)
      (M := realModule) (N := coordinateModule) infiniteCoordinates
  let b : regularIntegerCoefficients →ₗ[ℤ] (realModule →L[ℤ] coordinateModule) :=
    (ContinuousLinearMap.lcomp coordinateModule realDoubling).comp
      (q.comp (infiniteBasisInclusion k))
  constructor
  · calc
      _ = q (infiniteBasisInclusion k r) (realDoubling m) i +
          q (infiniteBasisInclusion k s) (realDoubling n) i :=
        congrFun (((TopModuleCat.tensorLiftCLM ℤ (C := regularIntegerCoefficients)
          (M := realModule) (N := coordinateModule) b).map_add
          (show TopModuleCat.tensorLeftObj ℤ regularIntegerCoefficients realModule from
            r ⊗ₜ[ℤ] m)
          (show TopModuleCat.tensorLeftObj ℤ regularIntegerCoefficients realModule from
            s ⊗ₜ[ℤ] n)).trans
          (congrArg₂ (fun x y : coordinateModule ↦ x + y)
            (TopModuleCat.tensorLiftCLM_tmul ℤ (C := regularIntegerCoefficients)
              (M := realModule) (N := coordinateModule) b r m)
            (TopModuleCat.tensorLiftCLM_tmul ℤ (C := regularIntegerCoefficients)
              (M := realModule) (N := coordinateModule) b s n))) i
      _ = r • infiniteCoordinates (integerBasisVector k ⊗ₜ[ℤ] realDoubling m) i +
          s • infiniteCoordinates (integerBasisVector k ⊗ₜ[ℤ] realDoubling n) i := by
        apply congrArg₂ (fun x y : realModule ↦ x + y)
        · calc
            _ = q (r • integerBasisVector k) (realDoubling m) i :=
              congrArg (fun d : infiniteCoefficients ↦ q d (realDoubling m) i)
                (LinearMap.smulRight_apply
                  (LinearMap.id : regularIntegerCoefficients →ₗ[ℤ] ℤ) (integerBasisVector k) r)
            _ = r • q (integerBasisVector k) (realDoubling m) i :=
              congrFun (DFunLike.congr_fun (q.map_smul r (integerBasisVector k))
                (realDoubling m)) i
            _ = _ := congrArg (fun x : coordinateModule ↦ r • x i)
              (TopModuleCat.tensorCurry_apply_apply ℤ (C := infiniteCoefficients)
                (M := realModule) (N := coordinateModule) infiniteCoordinates
                (integerBasisVector k) (realDoubling m))
        · calc
            _ = q (s • integerBasisVector k) (realDoubling n) i :=
              congrArg (fun d : infiniteCoefficients ↦ q d (realDoubling n) i)
                (LinearMap.smulRight_apply
                  (LinearMap.id : regularIntegerCoefficients →ₗ[ℤ] ℤ) (integerBasisVector k) s)
            _ = s • q (integerBasisVector k) (realDoubling n) i :=
              congrFun (DFunLike.congr_fun (q.map_smul s (integerBasisVector k))
                (realDoubling n)) i
            _ = _ := congrArg (fun x : coordinateModule ↦ s • x i)
              (TopModuleCat.tensorCurry_apply_apply ℤ (C := infiniteCoefficients)
                (M := realModule) (N := coordinateModule) infiniteCoordinates
                (integerBasisVector k) (realDoubling n))
      _ = r • (if k = i then realDoubling m else 0) +
          s • (if k = i then realDoubling n else 0) :=
        congrArg₂ (fun x y : realModule ↦ r • x + s • y)
          (infiniteCoordinates_basis_tmul k i (realDoubling m))
          (infiniteCoordinates_basis_tmul k i (realDoubling n))
      _ = _ := by
        by_cases h : k = i
        · simp only [ite_eq_left h, realDoubling, smul_apply, ContinuousLinearMap.id_apply]
        · simp only [ite_eq_right h, smul_zero, add_zero]
  · constructor
    · calc
        _ = infiniteCoordinates
            (integerBasisVector 0 ⊗ₜ[ℤ] m + integerBasisVector 1 ⊗ₜ[ℤ] n) i :=
          (ContinuousLinearMap.comp_apply (coordinateReadout i) infiniteCoordinates
            (show infiniteTensor from
              integerBasisVector 0 ⊗ₜ[ℤ] m + integerBasisVector 1 ⊗ₜ[ℤ] n)).trans
            (ContinuousLinearMap.proj_apply (R := ℤ) (φ := fun _ : ℕ ↦ realModule) i _)
        _ = infiniteCoordinates (integerBasisVector 0 ⊗ₜ[ℤ] m) i +
            infiniteCoordinates (integerBasisVector 1 ⊗ₜ[ℤ] n) i :=
          congrFun (infiniteCoordinates.map_add
            (show infiniteTensor from integerBasisVector 0 ⊗ₜ[ℤ] m)
            (show infiniteTensor from integerBasisVector 1 ⊗ₜ[ℤ] n)) i
        _ = _ := congrArg₂ (fun x y : realModule ↦ x + y)
          (infiniteCoordinates_basis_tmul 0 i m)
          (infiniteCoordinates_basis_tmul 1 i n)
    · calc
        _ = (coordinateReadout i) (infiniteCoordinates (c ⊗ₜ[ℤ] m)) :=
          (TopModuleCat.tensorCurry_apply_apply ℤ (C := infiniteCoefficients)
            (M := realModule) (N := realModule)
            ((coordinateReadout i).comp infiniteCoordinates) c m).trans
            (ContinuousLinearMap.comp_apply (coordinateReadout i) infiniteCoordinates
              (show infiniteTensor from c ⊗ₜ[ℤ] m))
        _ = infiniteCoordinates (c ⊗ₜ[ℤ] m) i :=
          ContinuousLinearMap.proj_apply (R := ℤ) (φ := fun _ : ℕ ↦ realModule) i _
        _ = _ := TopModuleCat.tensorCoordinatesCLM_tmul_apply ℤ
          infiniteCoefficients realModule infiniteBasis c m i

/-- The fixed retraction and nonidentity right doubling commute with any ideal-family lift. -/
theorem firstAxis_lift_restriction
    (b : firstAxisCoefficients →ₗ[productRing]
      (productModule →L[productRing] productModule)) :
    TopModuleCat.tensorLiftCLM productRing (C := ModuleCat.of productRing productRing)
        ((ContinuousLinearMap.lcomp productModule productDoubling).comp
          (b.comp firstAxisRetraction)) =
      (TopModuleCat.tensorLiftCLM productRing b).comp
        (TopModuleCat.tensorMapCLM productRing (C := ModuleCat.of productRing productRing)
          firstAxisRetraction productDoubling) := by
  exact TopModuleCat.tensorLiftCLM_comp_tensorMapCLM productRing
    (C := firstAxisCoefficients) (D := ModuleCat.of productRing productRing)
    (M := productModule) (N := productModule) (P := productModule)
    b firstAxisRetraction productDoubling

/-- Doubling the target postcomposes every curried family on the nonfree ideal tensor. -/
theorem firstAxis_curry_postdoubling
    (f : firstAxisTensorObj →L[productRing] productModule) :
    TopModuleCat.tensorCurry productRing (productDoubling.comp f) =
      ((ContinuousLinearMap.llcomp productRing productModule productModule productModule).flip
        productDoubling).comp (TopModuleCat.tensorCurry productRing f) := by
  exact TopModuleCat.tensorCurry_comp productRing (C := firstAxisCoefficients)
    (M := productModule) (N := productModule) (P := productModule) f productDoubling

/-- The ideal restriction acts on variable regular mixed tensors;
target doubling acts on arbitrary ideal-coefficient detector values. -/
theorem firstAxis_restriction_values (r s : productRing) (m n : productModule)
    (c : firstAxisCoefficients) :
    TopModuleCat.tensorLiftCLM productRing (C := ModuleCat.of productRing productRing)
        ((ContinuousLinearMap.lcomp productModule productDoubling).comp
          (firstAxisPairing.comp firstAxisRetraction))
        (r ⊗ₜ[productRing] m + s ⊗ₜ[productRing] n) =
      (r * firstAxisIdempotent) * (2 * m) + (s * firstAxisIdempotent) * (2 * n) ∧
    TopModuleCat.tensorCurry productRing (productDoubling.comp firstAxisTensorValue) c m =
      2 * ((c : productRing) * m) := by
  let b : ModuleCat.of productRing productRing →ₗ[productRing]
      (productModule →L[productRing] productModule) :=
    (ContinuousLinearMap.lcomp productModule productDoubling).comp
      (firstAxisPairing.comp firstAxisRetraction)
  constructor
  · calc
      _ = firstAxisPairing (firstAxisRetraction r) (productDoubling m) +
          firstAxisPairing (firstAxisRetraction s) (productDoubling n) :=
        ((TopModuleCat.tensorLiftCLM productRing (C := ModuleCat.of productRing productRing)
          (M := productModule) (N := productModule) b).map_add
          (show TopModuleCat.tensorLeftObj productRing
              (ModuleCat.of productRing productRing) productModule from r ⊗ₜ[productRing] m)
          (show TopModuleCat.tensorLeftObj productRing
              (ModuleCat.of productRing productRing) productModule from s ⊗ₜ[productRing] n)).trans
          (congrArg₂ (fun x y : productModule ↦ x + y)
            (TopModuleCat.tensorLiftCLM_tmul productRing
              (C := ModuleCat.of productRing productRing) (M := productModule)
              (N := productModule) b r m)
            (TopModuleCat.tensorLiftCLM_tmul productRing
              (C := ModuleCat.of productRing productRing) (M := productModule)
              (N := productModule) b s n))
      _ = (firstAxisRetraction r : productRing) * productDoubling m +
          (firstAxisRetraction s : productRing) * productDoubling n :=
        congrArg₂ (fun x y : productModule ↦ x + y)
          ((DFunLike.congr_fun (LinearMap.smulRight_apply firstAxisIdeal.subtype
            (ContinuousLinearMap.id productRing productModule) (firstAxisRetraction r))
            (productDoubling m)).trans
            (by simp only [smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul,
              Submodule.subtype_apply]))
          ((DFunLike.congr_fun (LinearMap.smulRight_apply firstAxisIdeal.subtype
            (ContinuousLinearMap.id productRing productModule) (firstAxisRetraction s))
            (productDoubling n)).trans
            (by simp only [smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul,
              Submodule.subtype_apply]))
      _ = (r * firstAxisIdempotent) * productDoubling m +
          (s * firstAxisIdempotent) * productDoubling n :=
        congrArg₂ (fun x y : productRing ↦ x * productDoubling m + y * productDoubling n)
          ((LinearMap.codRestrict_apply firstAxisIdeal
            (LinearMap.toSpanSingleton productRing productRing firstAxisIdempotent)
            (h := fun a ↦ (firstAxisRetraction a).property) r).trans
            (by simp only [LinearMap.toSpanSingleton_apply, smul_eq_mul]))
          ((LinearMap.codRestrict_apply firstAxisIdeal
            (LinearMap.toSpanSingleton productRing productRing firstAxisIdempotent)
            (h := fun a ↦ (firstAxisRetraction a).property) s).trans
            (by simp only [LinearMap.toSpanSingleton_apply, smul_eq_mul]))
      _ = _ := by
        simp only [productDoubling, smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
  · calc
      _ = productDoubling (firstAxisTensorValue (c ⊗ₜ[productRing] m)) :=
        (TopModuleCat.tensorCurry_apply_apply productRing (C := firstAxisCoefficients)
          (M := productModule) (N := productModule)
          (productDoubling.comp firstAxisTensorValue) c m).trans
          (ContinuousLinearMap.comp_apply productDoubling firstAxisTensorValue
            (show firstAxisTensorObj from c ⊗ₜ[productRing] m))
      _ = productDoubling ((c : productRing) * m) :=
        congrArg productDoubling
          ((TopModuleCat.tensorLiftCLM_tmul productRing (C := firstAxisCoefficients)
            (M := productModule) (N := productModule)
            (firstAxisIdeal.subtype.smulRight
              (ContinuousLinearMap.id productRing productModule)) c m).trans
            ((DFunLike.congr_fun (LinearMap.smulRight_apply firstAxisIdeal.subtype
              (ContinuousLinearMap.id productRing productModule) c) m).trans
              (by simp only [smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul,
                Submodule.subtype_apply])))
      _ = _ := by
        simp only [productDoubling, smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]

/-- Nonzero and distinct behavior of the integer dot and cross detectors. -/
theorem integerControlValues :
    TensorHomExamples.integerDotTensor TensorHomExamples.integerFirstTensor = 1 ∧
    TensorHomExamples.integerDotTensor TensorHomExamples.integerCrossTensor = 0 ∧
    TensorHomExamples.integerSecondProjectionTensor TensorHomExamples.integerCrossTensor = 1 ∧
    TensorHomExamples.integerCrossTensor ≠ 0 ∧
    TensorHomExamples.integerTensorDoubling TensorHomExamples.integerFirstTensor ≠
      TensorHomExamples.integerFirstTensor :=
  ⟨TensorHomExamples.integerDotTensor_first,
    TensorHomExamples.integerDotTensor_cross,
    TensorHomExamples.integerSecondProjectionTensor_cross,
    TensorHomExamples.integerCrossTensor_ne_zero,
    TensorHomExamples.integerTensorDoubling_first_ne⟩

/-- Nonfinite coefficients, nondiscrete right topology, and detected mixed values. -/
theorem infiniteControlValues :
    (¬ Module.Finite ℤ ProjectiveTensorSeparationExamples.infiniteCoefficients) ∧
    (¬ DiscreteTopology ProjectiveTensorSeparationExamples.realModule) ∧
    ProjectiveTensorSeparationExamples.infiniteFirstTensor ≠ 0 ∧
    ProjectiveTensorSeparationExamples.infiniteMixedX ≠
      ProjectiveTensorSeparationExamples.infiniteMixedY ∧
    (ProjectiveTensorSeparationExamples.infiniteCoordinates
        ProjectiveTensorSeparationExamples.infiniteMixedX 0 = 1 ∧
      ProjectiveTensorSeparationExamples.infiniteCoordinates
        ProjectiveTensorSeparationExamples.infiniteMixedX 1 = 2) ∧
    (ProjectiveTensorSeparationExamples.infiniteCoordinates
        ProjectiveTensorSeparationExamples.infiniteMixedY 0 = 2 ∧
      ProjectiveTensorSeparationExamples.infiniteCoordinates
        ProjectiveTensorSeparationExamples.infiniteMixedY 1 = 1) :=
  ⟨ProjectiveTensorSeparationExamples.infiniteCoefficients_not_finite,
    ProjectiveTensorSeparationExamples.realModule_not_discrete,
    ProjectiveTensorSeparationExamples.infiniteFirstTensor_ne_zero,
    ProjectiveTensorSeparationExamples.infiniteMixedX_ne_mixedY,
    ProjectiveTensorSeparationExamples.infiniteMixedX_coordinates,
    ProjectiveTensorSeparationExamples.infiniteMixedY_coordinates⟩

/-- The ideal is nonfree and nontrivial and its outgoing map detects a nonzero tensor. -/
theorem firstAxisControlValues :
    (¬ Module.Free ProjectiveTensorSeparationExamples.productRing
      ProjectiveTensorSeparationExamples.firstAxisCoefficients) ∧
    Nontrivial ProjectiveTensorSeparationExamples.firstAxisCoefficients ∧
    ProjectiveTensorSeparationExamples.firstAxisElement ≠ 0 ∧
    ProjectiveTensorSeparationExamples.firstAxisTensor ≠ 0 ∧
    ProjectiveTensorSeparationExamples.firstAxisTensorValue
        ProjectiveTensorSeparationExamples.firstAxisTensor =
      ProjectiveTensorSeparationExamples.firstAxisIdempotent :=
  ⟨ProjectiveTensorSeparationExamples.firstAxisCoefficients_not_free,
    ProjectiveTensorSeparationExamples.firstAxisCoefficients_nontrivial,
    ProjectiveTensorSeparationExamples.firstAxisElement_ne_zero,
    ProjectiveTensorSeparationExamples.firstAxisTensor_ne_zero,
    ProjectiveTensorSeparationExamples.firstAxisTensorValue_first⟩

end TensorHomNaturalityExamples
