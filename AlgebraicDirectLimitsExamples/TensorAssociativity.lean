/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicDirectLimits.Topology.TensorAssociativity
public import AlgebraicDirectLimitsExamples.ProjectiveTensorSeparation
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.Topology.Algebra.Group.ZPow
public import Mathlib.Topology.Instances.Int
public import Mathlib.Topology.Instances.ZMod

/-!
# Detected tensor reassociation over the integers

Rank-two integer modules give nonzero tensors in both parenthesizations. Bundled
algebraic detectors read products of three coordinates, without a continuity
assumption on the detectors. Reassociation and its inverse transport these
values. Mixed coefficients retain two distinct components; scalar doubling,
coefficient swaps and the commutation of the flat coefficient tensor give
observable nonidentity maps.

The torsion module `ZMod 3`, regarded as an integer module rather than a module
over a field, gives nonfree nonzero coefficients. `Fin 0 → ℤ` is a singleton
zero module and supplies a separate boundary. The supplied right modules use
their usual discrete or product-discrete topologies; discreteness is not a
hypothesis of the general associator.

## References

The detectors reuse Mathlib's algebraic tensor lift by Kenny Lau and Mario
Carneiro and bilinear multiplication by Kenny Lau and Yury Kudryashov.
Reassociation and tensor maps reuse Kenny Lau and Mario Carneiro's API and
Formal Frontier Agents' one-sided tensor construction, following Beacon's
topological ideas. The topological-module foundation is due to Richard Hill and
Andrew Yang. The module-product API is due to Johannes Hölzl, Mario Carneiro,
Kevin Buzzard, Yury Kudryashov and Eric Wieser. The discrete integer topology is
due to Johannes Hölzl and Mario Carneiro; integer-action continuity additionally
credits Patrick Massot. The discrete `ZMod` topology is due to David Loeffler.
The continuous-linear-equivalence contributors are credited in
`AlgebraicDirectLimits.Topology.TensorAssociativity`.
-/

@[expose] public section

open scoped TensorProduct

namespace TensorAssociativityExamples

/-- The algebraic rank-two integer coefficients. -/
abbrev integerPairCoefficients : ModuleCat ℤ := ModuleCat.of ℤ (ℤ × ℤ)

/-- The rank-two integer right factor with its product-discrete topology. -/
abbrev integerPairModule : TopModuleCat ℤ := TopModuleCat.of ℤ (ℤ × ℤ)

/-- The left-parenthesized tensor of two rank-two integer coefficient modules
and the supplied rank-two topological right factor. -/
noncomputable abbrev PairLeft := TopModuleCat.tensorLeftObj ℤ
  (ModuleCat.of ℤ (integerPairCoefficients ⊗[ℤ] integerPairCoefficients)) integerPairModule
/-- The right-parenthesized tensor, with the inner tensor using the supplied
rank-two topological right factor. -/
noncomputable abbrev PairRight := TopModuleCat.tensorLeftObj ℤ integerPairCoefficients
  (TopModuleCat.tensorLeftObj ℤ integerPairCoefficients integerPairModule)

/-- The supplied integer-pair associator. -/
noncomputable def integerPairAssoc : PairLeft ≃L[ℤ] PairRight :=
  TopModuleCat.tensorAssocContinuousLinearEquiv ℤ
    integerPairCoefficients integerPairCoefficients integerPairModule

/-- The first coordinate vector. -/
def e1 : ℤ × ℤ := (1, 0)

/-- The second coordinate vector. -/
def e2 : ℤ × ℤ := (0, 1)

/-- A left-parenthesized triple with different coefficient directions. -/
noncomputable def leftTriple : PairLeft := (e1 ⊗ₜ[ℤ] e2) ⊗ₜ[ℤ] e1

/-- The corresponding right-parenthesized triple. -/
noncomputable def rightTriple : PairRight := e1 ⊗ₜ[ℤ] (e2 ⊗ₜ[ℤ] e1)

/-- Forward transport of the integer triple. -/
noncomputable def forwardTriple : PairRight := integerPairAssoc leftTriple

/-- Inverse transport of the nested integer triple. -/
noncomputable def inverseTriple : PairLeft := integerPairAssoc.symm rightTriple

/-- The canonical integer-linear projection onto the first coordinate. -/
abbrev p1 : (ℤ × ℤ) →ₗ[ℤ] ℤ := LinearMap.fst ℤ ℤ ℤ
/-- The canonical integer-linear projection onto the second coordinate. -/
abbrev p2 : (ℤ × ℤ) →ₗ[ℤ] ℤ := LinearMap.snd ℤ ℤ ℤ

/-- The algebraic detector on a left-parenthesized tensor obtained by lifting
`(c, d, m) ↦ (p c * q d) * r m`; no continuity is asserted. -/
noncomputable def leftDetector
    (p q r : (ℤ × ℤ) →ₗ[ℤ] ℤ) : PairLeft →ₗ[ℤ] ℤ :=
  TensorProduct.lift ((LinearMap.mul ℤ ℤ).compl₁₂
    (TensorProduct.lift ((LinearMap.mul ℤ ℤ).compl₁₂ p q)) r)

/-- The left detector evaluates a pure triple as the left-associated product
of the three selected linear forms. -/
theorem leftDetector_tmul (p q r : (ℤ × ℤ) →ₗ[ℤ] ℤ) (c d m : ℤ × ℤ) :
    leftDetector p q r ((c ⊗ₜ[ℤ] d) ⊗ₜ[ℤ] m) = (p c * q d) * r m := by
  calc
    leftDetector p q r ((c ⊗ₜ[ℤ] d) ⊗ₜ[ℤ] m) =
        (LinearMap.mul ℤ ℤ).compl₁₂
          (TensorProduct.lift ((LinearMap.mul ℤ ℤ).compl₁₂ p q)) r
          (c ⊗ₜ[ℤ] d) m :=
      TensorProduct.lift.tmul
        (f' := (LinearMap.mul ℤ ℤ).compl₁₂
          (TensorProduct.lift ((LinearMap.mul ℤ ℤ).compl₁₂ p q)) r)
        (c ⊗ₜ[ℤ] d) m
    _ = (p c * q d) * r m := by
      rw [LinearMap.compl₁₂_apply, LinearMap.mul_apply',
        TensorProduct.lift.tmul (f' := (LinearMap.mul ℤ ℤ).compl₁₂ p q) c d,
        LinearMap.compl₁₂_apply, LinearMap.mul_apply']

/-- The algebraic detector on a right-parenthesized tensor obtained by lifting
`(c, d, m) ↦ p c * (q d * r m)`; no continuity is asserted. -/
noncomputable def rightDetector
    (p q r : (ℤ × ℤ) →ₗ[ℤ] ℤ) : PairRight →ₗ[ℤ] ℤ :=
  TensorProduct.lift ((LinearMap.mul ℤ ℤ).compl₁₂ p
    (TensorProduct.lift ((LinearMap.mul ℤ ℤ).compl₁₂ q r)))

/-- The right detector evaluates a pure triple as the right-associated product
of the three selected linear forms. -/
theorem rightDetector_tmul (p q r : (ℤ × ℤ) →ₗ[ℤ] ℤ) (c d m : ℤ × ℤ) :
    rightDetector p q r (c ⊗ₜ[ℤ] (d ⊗ₜ[ℤ] m)) = p c * (q d * r m) := by
  calc
    rightDetector p q r (c ⊗ₜ[ℤ] (d ⊗ₜ[ℤ] m)) =
        (LinearMap.mul ℤ ℤ).compl₁₂ p
          (TensorProduct.lift ((LinearMap.mul ℤ ℤ).compl₁₂ q r))
          c (d ⊗ₜ[ℤ] m) :=
      TensorProduct.lift.tmul
        (f' := (LinearMap.mul ℤ ℤ).compl₁₂ p
          (TensorProduct.lift ((LinearMap.mul ℤ ℤ).compl₁₂ q r)))
        c (d ⊗ₜ[ℤ] m)
    _ = p c * (q d * r m) := by
      rw [LinearMap.compl₁₂_apply, LinearMap.mul_apply',
        TensorProduct.lift.tmul (f' := (LinearMap.mul ℤ ℤ).compl₁₂ q r) d m,
        LinearMap.compl₁₂_apply, LinearMap.mul_apply']

/-- The left detector for the product `c₁ d₂ m₁`. -/
noncomputable def leftDetection12 : PairLeft →ₗ[ℤ] ℤ := leftDetector p1 p2 p1

/-- The right detector for the product `c₁ d₂ m₁`. -/
noncomputable def rightDetection12 : PairRight →ₗ[ℤ] ℤ := rightDetector p1 p2 p1

/-- The left detector for the product `c₂ d₁ m₁`. -/
noncomputable def leftDetection21 : PairLeft →ₗ[ℤ] ℤ := leftDetector p2 p1 p1

/-- The right detector for the product `c₂ d₁ m₁`. -/
noncomputable def rightDetection21 : PairRight →ₗ[ℤ] ℤ := rightDetector p2 p1 p1

/-- The forward and inverse associator are exercised on the two pure triples. -/
theorem integerPair_forward_inverse :
    forwardTriple = rightTriple ∧ inverseTriple = leftTriple := by
  constructor
  · change (TopModuleCat.tensorAssocContinuousLinearEquiv ℤ
        integerPairCoefficients integerPairCoefficients integerPairModule)
        (show TopModuleCat.tensorLeftObj ℤ
            (ModuleCat.of ℤ (integerPairCoefficients ⊗[ℤ] integerPairCoefficients))
            integerPairModule from
          (e1 ⊗ₜ[ℤ] e2) ⊗ₜ[ℤ] e1) =
        (show TopModuleCat.tensorLeftObj ℤ integerPairCoefficients
            (TopModuleCat.tensorLeftObj ℤ integerPairCoefficients integerPairModule) from
          e1 ⊗ₜ[ℤ] (e2 ⊗ₜ[ℤ] e1))
    exact (TopModuleCat.tensorAssocContinuousLinearEquiv_apply ℤ
      integerPairCoefficients integerPairCoefficients integerPairModule _).trans
        (TensorProduct.assoc_tmul (R := ℤ) e1 e2 e1)
  · change (TopModuleCat.tensorAssocContinuousLinearEquiv ℤ
        integerPairCoefficients integerPairCoefficients integerPairModule).symm
        (show TopModuleCat.tensorLeftObj ℤ integerPairCoefficients
            (TopModuleCat.tensorLeftObj ℤ integerPairCoefficients integerPairModule) from
          e1 ⊗ₜ[ℤ] (e2 ⊗ₜ[ℤ] e1)) =
        (show TopModuleCat.tensorLeftObj ℤ
            (ModuleCat.of ℤ (integerPairCoefficients ⊗[ℤ] integerPairCoefficients))
            integerPairModule from
          (e1 ⊗ₜ[ℤ] e2) ⊗ₜ[ℤ] e1)
    exact (TopModuleCat.tensorAssocContinuousLinearEquiv_symm_apply ℤ
      integerPairCoefficients integerPairCoefficients integerPairModule _).trans
        (TensorProduct.assoc_symm_tmul (R := ℤ) e1 e2 e1)

/-- The two algebraic lifts read the three specified coordinates in either
parenthesization, with all three input vectors varying. -/
theorem integerPair_detector_coordinates (c d m : ℤ × ℤ) :
    leftDetection12 ((c ⊗ₜ[ℤ] d) ⊗ₜ[ℤ] m) = c.1 * d.2 * m.1 ∧
      rightDetection12 (c ⊗ₜ[ℤ] (d ⊗ₜ[ℤ] m)) = c.1 * d.2 * m.1 ∧
      leftDetector p1 p2 p2 ((c ⊗ₜ[ℤ] d) ⊗ₜ[ℤ] m) = c.1 * d.2 * m.2 ∧
      rightDetector p1 p2 p2 (c ⊗ₜ[ℤ] (d ⊗ₜ[ℤ] m)) = c.1 * d.2 * m.2 ∧
      leftDetector p2 p1 p2 ((c ⊗ₜ[ℤ] d) ⊗ₜ[ℤ] m) = c.2 * d.1 * m.2 ∧
      rightDetector p2 p1 p2 (c ⊗ₜ[ℤ] (d ⊗ₜ[ℤ] m)) = c.2 * d.1 * m.2 := by
  have hleft12 : leftDetection12 (show PairLeft from (c ⊗ₜ[ℤ] d) ⊗ₜ[ℤ] m) =
      c.1 * d.2 * m.1 := leftDetector_tmul p1 p2 p1 c d m
  have hright12 : rightDetection12 (show PairRight from c ⊗ₜ[ℤ] (d ⊗ₜ[ℤ] m)) =
      c.1 * (d.2 * m.1) := rightDetector_tmul p1 p2 p1 c d m
  have hleft122 : leftDetector p1 p2 p2 (show PairLeft from (c ⊗ₜ[ℤ] d) ⊗ₜ[ℤ] m) =
      c.1 * d.2 * m.2 := leftDetector_tmul p1 p2 p2 c d m
  have hright122 : rightDetector p1 p2 p2 (show PairRight from c ⊗ₜ[ℤ] (d ⊗ₜ[ℤ] m)) =
      c.1 * (d.2 * m.2) := rightDetector_tmul p1 p2 p2 c d m
  have hleft212 : leftDetector p2 p1 p2 (show PairLeft from (c ⊗ₜ[ℤ] d) ⊗ₜ[ℤ] m) =
      c.2 * d.1 * m.2 := leftDetector_tmul p2 p1 p2 c d m
  have hright212 : rightDetector p2 p1 p2 (show PairRight from c ⊗ₜ[ℤ] (d ⊗ₜ[ℤ] m)) =
      c.2 * (d.1 * m.2) := rightDetector_tmul p2 p1 p2 c d m
  exact ⟨hleft12, hright12.trans (mul_assoc c.1 d.2 m.1).symm,
    hleft122, hright122.trans (mul_assoc c.1 d.2 m.2).symm,
    hleft212, hright212.trans (mul_assoc c.2 d.1 m.2).symm⟩

/-- Both triple tensors have detector value one and are nonzero. -/
theorem integerPair_nonzero :
    leftDetection12 leftTriple = 1 ∧ rightDetection12 rightTriple = 1 ∧
      leftTriple ≠ 0 ∧ rightTriple ≠ 0 := by
  have hleft : leftDetection12 leftTriple = 1 := by
    simpa [leftTriple, e1, e2] using (integerPair_detector_coordinates e1 e2 e1).1
  have hright : rightDetection12 rightTriple = 1 := by
    simpa [rightTriple, e1, e2] using (integerPair_detector_coordinates e1 e2 e1).2.1
  refine ⟨hleft, hright, ?_, ?_⟩
  · intro h
    have hzero : (1 : ℤ) = 0 := hleft.symm.trans (by rw [h, map_zero])
    exact one_ne_zero hzero
  · intro h
    have hzero : (1 : ℤ) = 0 := hright.symm.trans (by rw [h, map_zero])
    exact one_ne_zero hzero

/-- The sum of the two pure coefficients with opposite coordinate directions,
`e1 ⊗ e2 + e2 ⊗ e1`. -/
noncomputable def mixedCoefficient :
    integerPairCoefficients ⊗[ℤ] integerPairCoefficients :=
  e1 ⊗ₜ[ℤ] e2 + e2 ⊗ₜ[ℤ] e1

/-- A mixed flat coefficient with a varying right input. -/
noncomputable def mixedLeft (m : ℤ × ℤ) : PairLeft := mixedCoefficient ⊗ₜ[ℤ] m

/-- The sum of the two corresponding nested components. -/
noncomputable def mixedRight (m : ℤ × ℤ) : PairRight :=
  e1 ⊗ₜ[ℤ] (e2 ⊗ₜ[ℤ] m) + e2 ⊗ₜ[ℤ] (e1 ⊗ₜ[ℤ] m)

/-- The mixed coefficient has two detected components, and the inverse
reconstructs it. The weighted detector distinguishes the two weights. -/
theorem integerPair_mixed :
    integerPairAssoc (mixedLeft e1) = mixedRight e1 ∧
      integerPairAssoc.symm (mixedRight e1) = mixedLeft e1 ∧
      leftDetection12 (mixedLeft e1) = 1 ∧ leftDetection21 (mixedLeft e1) = 1 ∧
      rightDetection12 (mixedRight e1) = 1 ∧ rightDetection21 (mixedRight e1) = 1 ∧
      (rightDetection12 + (2 : ℤ) • rightDetection21) (mixedRight e1) = 3 := by
  have htmul (c d m : ℤ × ℤ) :
      integerPairAssoc ((c ⊗ₜ[ℤ] d) ⊗ₜ[ℤ] m) = c ⊗ₜ[ℤ] (d ⊗ₜ[ℤ] m) := by
    change (TopModuleCat.tensorAssocContinuousLinearEquiv ℤ
        integerPairCoefficients integerPairCoefficients integerPairModule)
        (show TopModuleCat.tensorLeftObj ℤ
            (ModuleCat.of ℤ (integerPairCoefficients ⊗[ℤ] integerPairCoefficients))
            integerPairModule from
          (c ⊗ₜ[ℤ] d) ⊗ₜ[ℤ] m) =
        (show TopModuleCat.tensorLeftObj ℤ integerPairCoefficients
            (TopModuleCat.tensorLeftObj ℤ integerPairCoefficients integerPairModule) from
          c ⊗ₜ[ℤ] (d ⊗ₜ[ℤ] m))
    exact (TopModuleCat.tensorAssocContinuousLinearEquiv_apply ℤ
      integerPairCoefficients integerPairCoefficients integerPairModule
      (show PairLeft from (c ⊗ₜ[ℤ] d) ⊗ₜ[ℤ] m)).trans
        (TensorProduct.assoc_tmul (R := ℤ) c d m)
  have hsum : (show PairLeft from
      (e1 ⊗ₜ[ℤ] e2 + e2 ⊗ₜ[ℤ] e1) ⊗ₜ[ℤ] e1) =
      (show PairLeft from (e1 ⊗ₜ[ℤ] e2) ⊗ₜ[ℤ] e1) +
        (show PairLeft from (e2 ⊗ₜ[ℤ] e1) ⊗ₜ[ℤ] e1) :=
    TensorProduct.add_tmul (R := ℤ) (e1 ⊗ₜ[ℤ] e2) (e2 ⊗ₜ[ℤ] e1) e1
  have hforward : integerPairAssoc (mixedLeft e1) = mixedRight e1 := by
    have hadd : integerPairAssoc
        ((show PairLeft from (e1 ⊗ₜ[ℤ] e2) ⊗ₜ[ℤ] e1) +
          (show PairLeft from (e2 ⊗ₜ[ℤ] e1) ⊗ₜ[ℤ] e1)) =
        integerPairAssoc (show PairLeft from (e1 ⊗ₜ[ℤ] e2) ⊗ₜ[ℤ] e1) +
          integerPairAssoc (show PairLeft from (e2 ⊗ₜ[ℤ] e1) ⊗ₜ[ℤ] e1) :=
      ContinuousLinearEquiv.map_add integerPairAssoc
        (show PairLeft from (e1 ⊗ₜ[ℤ] e2) ⊗ₜ[ℤ] e1)
        (show PairLeft from (e2 ⊗ₜ[ℤ] e1) ⊗ₜ[ℤ] e1)
    exact (congrArg integerPairAssoc hsum).trans
      (hadd.trans (congrArg₂ (fun x y : PairRight ↦ x + y)
        (htmul e1 e2 e1) (htmul e2 e1 e1)))
  have hinverse : integerPairAssoc.symm (mixedRight e1) = mixedLeft e1 :=
    (congrArg integerPairAssoc.symm hforward.symm).trans
      (integerPairAssoc.symm_apply_apply (mixedLeft e1))
  have hleft12 : leftDetection12 (mixedLeft e1) = 1 := by
    have hadd : leftDetection12 ((show PairLeft from (e1 ⊗ₜ[ℤ] e2) ⊗ₜ[ℤ] e1) +
        (show PairLeft from (e2 ⊗ₜ[ℤ] e1) ⊗ₜ[ℤ] e1)) =
        leftDetection12 (show PairLeft from (e1 ⊗ₜ[ℤ] e2) ⊗ₜ[ℤ] e1) +
          leftDetection12 (show PairLeft from (e2 ⊗ₜ[ℤ] e1) ⊗ₜ[ℤ] e1) :=
      (leftDetection12).map_add (show PairLeft from (e1 ⊗ₜ[ℤ] e2) ⊗ₜ[ℤ] e1)
        (show PairLeft from (e2 ⊗ₜ[ℤ] e1) ⊗ₜ[ℤ] e1)
    have hpure : leftDetection12 (show PairLeft from (e1 ⊗ₜ[ℤ] e2) ⊗ₜ[ℤ] e1) +
        leftDetection12 (show PairLeft from (e2 ⊗ₜ[ℤ] e1) ⊗ₜ[ℤ] e1) =
        (p1 e1 * p2 e2) * p1 e1 + (p1 e2 * p2 e1) * p1 e1 :=
      congrArg₂ (fun x y : ℤ ↦ x + y)
        (leftDetector_tmul p1 p2 p1 e1 e2 e1)
        (leftDetector_tmul p1 p2 p1 e2 e1 e1)
    exact (congrArg (leftDetection12) hsum).trans
      (hadd.trans (hpure.trans (by simp [p1, p2, e1, e2])))
  have hleft21 : leftDetection21 (mixedLeft e1) = 1 := by
    have hadd : leftDetection21 ((show PairLeft from (e1 ⊗ₜ[ℤ] e2) ⊗ₜ[ℤ] e1) +
        (show PairLeft from (e2 ⊗ₜ[ℤ] e1) ⊗ₜ[ℤ] e1)) =
        leftDetection21 (show PairLeft from (e1 ⊗ₜ[ℤ] e2) ⊗ₜ[ℤ] e1) +
          leftDetection21 (show PairLeft from (e2 ⊗ₜ[ℤ] e1) ⊗ₜ[ℤ] e1) :=
      (leftDetection21).map_add (show PairLeft from (e1 ⊗ₜ[ℤ] e2) ⊗ₜ[ℤ] e1)
        (show PairLeft from (e2 ⊗ₜ[ℤ] e1) ⊗ₜ[ℤ] e1)
    have hpure : leftDetection21 (show PairLeft from (e1 ⊗ₜ[ℤ] e2) ⊗ₜ[ℤ] e1) +
        leftDetection21 (show PairLeft from (e2 ⊗ₜ[ℤ] e1) ⊗ₜ[ℤ] e1) =
        (p2 e1 * p1 e2) * p1 e1 + (p2 e2 * p1 e1) * p1 e1 :=
      congrArg₂ (fun x y : ℤ ↦ x + y)
        (leftDetector_tmul p2 p1 p1 e1 e2 e1)
        (leftDetector_tmul p2 p1 p1 e2 e1 e1)
    exact (congrArg (leftDetection21) hsum).trans
      (hadd.trans (hpure.trans (by simp [p1, p2, e1, e2])))
  have hright12 : rightDetection12 (mixedRight e1) = 1 := by
    have hadd : rightDetection12 ((show PairRight from e1 ⊗ₜ[ℤ] (e2 ⊗ₜ[ℤ] e1)) +
        (show PairRight from e2 ⊗ₜ[ℤ] (e1 ⊗ₜ[ℤ] e1))) =
        rightDetection12 (show PairRight from e1 ⊗ₜ[ℤ] (e2 ⊗ₜ[ℤ] e1)) +
          rightDetection12 (show PairRight from e2 ⊗ₜ[ℤ] (e1 ⊗ₜ[ℤ] e1)) :=
      (rightDetection12).map_add (show PairRight from e1 ⊗ₜ[ℤ] (e2 ⊗ₜ[ℤ] e1))
        (show PairRight from e2 ⊗ₜ[ℤ] (e1 ⊗ₜ[ℤ] e1))
    have hpure : rightDetection12 (show PairRight from e1 ⊗ₜ[ℤ] (e2 ⊗ₜ[ℤ] e1)) +
        rightDetection12 (show PairRight from e2 ⊗ₜ[ℤ] (e1 ⊗ₜ[ℤ] e1)) =
        p1 e1 * (p2 e2 * p1 e1) + p1 e2 * (p2 e1 * p1 e1) :=
      congrArg₂ (fun x y : ℤ ↦ x + y)
        (rightDetector_tmul p1 p2 p1 e1 e2 e1)
        (rightDetector_tmul p1 p2 p1 e2 e1 e1)
    exact hadd.trans (hpure.trans (by simp [p1, p2, e1, e2]))
  have hright21 : rightDetection21 (mixedRight e1) = 1 := by
    have hadd : rightDetection21 ((show PairRight from e1 ⊗ₜ[ℤ] (e2 ⊗ₜ[ℤ] e1)) +
        (show PairRight from e2 ⊗ₜ[ℤ] (e1 ⊗ₜ[ℤ] e1))) =
        rightDetection21 (show PairRight from e1 ⊗ₜ[ℤ] (e2 ⊗ₜ[ℤ] e1)) +
          rightDetection21 (show PairRight from e2 ⊗ₜ[ℤ] (e1 ⊗ₜ[ℤ] e1)) :=
      (rightDetection21).map_add (show PairRight from e1 ⊗ₜ[ℤ] (e2 ⊗ₜ[ℤ] e1))
        (show PairRight from e2 ⊗ₜ[ℤ] (e1 ⊗ₜ[ℤ] e1))
    have hpure : rightDetection21 (show PairRight from e1 ⊗ₜ[ℤ] (e2 ⊗ₜ[ℤ] e1)) +
        rightDetection21 (show PairRight from e2 ⊗ₜ[ℤ] (e1 ⊗ₜ[ℤ] e1)) =
        p2 e1 * (p1 e2 * p1 e1) + p2 e2 * (p1 e1 * p1 e1) :=
      congrArg₂ (fun x y : ℤ ↦ x + y)
        (rightDetector_tmul p2 p1 p1 e1 e2 e1)
        (rightDetector_tmul p2 p1 p1 e2 e1 e1)
    exact hadd.trans (hpure.trans (by simp [p1, p2, e1, e2]))
  have hweighted : (rightDetection12 + (2 : ℤ) • rightDetection21) (mixedRight e1) =
      rightDetection12 (mixedRight e1) + (2 : ℤ) • rightDetection21 (mixedRight e1) :=
    (LinearMap.add_apply rightDetection12 ((2 : ℤ) • rightDetection21)
      (mixedRight e1)).trans
        (congrArg (fun z : ℤ ↦ rightDetection12 (mixedRight e1) + z)
          (LinearMap.smul_apply (2 : ℤ) rightDetection21 (mixedRight e1)))
  refine ⟨hforward, hinverse, hleft12, hleft21, hright12, hright21, ?_⟩
  exact hweighted.trans
    ((congrArg₂ (fun x y : ℤ ↦ x + (2 : ℤ) • y) hright12 hright21).trans (by norm_num))

/-- The two right-input coordinates remain observable after reassociation of a
mixed coefficient; at `(1, 2)` the detector pair is `(1, 2)`. -/
theorem integerPair_variable_coordinates (s t : ℤ) :
    integerPairAssoc (mixedLeft (s, t)) = mixedRight (s, t) ∧
      leftDetection12 (mixedLeft (s, t)) = s ∧
      rightDetection12 (mixedRight (s, t)) = s ∧
      leftDetector p2 p1 p2 (mixedLeft (s, t)) = t ∧
      rightDetector p2 p1 p2 (mixedRight (s, t)) = t := by
  have htmul (c d m : ℤ × ℤ) :
      integerPairAssoc ((c ⊗ₜ[ℤ] d) ⊗ₜ[ℤ] m) = c ⊗ₜ[ℤ] (d ⊗ₜ[ℤ] m) := by
    change (TopModuleCat.tensorAssocContinuousLinearEquiv ℤ
        integerPairCoefficients integerPairCoefficients integerPairModule)
        (show TopModuleCat.tensorLeftObj ℤ
            (ModuleCat.of ℤ (integerPairCoefficients ⊗[ℤ] integerPairCoefficients))
            integerPairModule from
          (c ⊗ₜ[ℤ] d) ⊗ₜ[ℤ] m) =
        (show TopModuleCat.tensorLeftObj ℤ integerPairCoefficients
            (TopModuleCat.tensorLeftObj ℤ integerPairCoefficients integerPairModule) from
          c ⊗ₜ[ℤ] (d ⊗ₜ[ℤ] m))
    exact (TopModuleCat.tensorAssocContinuousLinearEquiv_apply ℤ
      integerPairCoefficients integerPairCoefficients integerPairModule
      (show PairLeft from (c ⊗ₜ[ℤ] d) ⊗ₜ[ℤ] m)).trans
        (TensorProduct.assoc_tmul (R := ℤ) c d m)
  have hsum : (show PairLeft from
      (e1 ⊗ₜ[ℤ] e2 + e2 ⊗ₜ[ℤ] e1) ⊗ₜ[ℤ] (s, t)) =
      (show PairLeft from (e1 ⊗ₜ[ℤ] e2) ⊗ₜ[ℤ] (s, t)) +
        (show PairLeft from (e2 ⊗ₜ[ℤ] e1) ⊗ₜ[ℤ] (s, t)) :=
    TensorProduct.add_tmul (R := ℤ) (e1 ⊗ₜ[ℤ] e2) (e2 ⊗ₜ[ℤ] e1) (s, t)
  have hforward : integerPairAssoc (mixedLeft (s, t)) = mixedRight (s, t) := by
    have hadd : integerPairAssoc
        ((show PairLeft from (e1 ⊗ₜ[ℤ] e2) ⊗ₜ[ℤ] (s, t)) +
          (show PairLeft from (e2 ⊗ₜ[ℤ] e1) ⊗ₜ[ℤ] (s, t))) =
        integerPairAssoc (show PairLeft from (e1 ⊗ₜ[ℤ] e2) ⊗ₜ[ℤ] (s, t)) +
          integerPairAssoc (show PairLeft from (e2 ⊗ₜ[ℤ] e1) ⊗ₜ[ℤ] (s, t)) :=
      ContinuousLinearEquiv.map_add integerPairAssoc
        (show PairLeft from (e1 ⊗ₜ[ℤ] e2) ⊗ₜ[ℤ] (s, t))
        (show PairLeft from (e2 ⊗ₜ[ℤ] e1) ⊗ₜ[ℤ] (s, t))
    exact (congrArg integerPairAssoc hsum).trans
      (hadd.trans (congrArg₂ (fun x y : PairRight ↦ x + y)
        (htmul e1 e2 (s, t)) (htmul e2 e1 (s, t))))
  have hleft12 : leftDetection12 (mixedLeft (s, t)) = s := by
    have hadd : leftDetection12 ((show PairLeft from (e1 ⊗ₜ[ℤ] e2) ⊗ₜ[ℤ] (s, t)) +
        (show PairLeft from (e2 ⊗ₜ[ℤ] e1) ⊗ₜ[ℤ] (s, t))) =
        leftDetection12 (show PairLeft from (e1 ⊗ₜ[ℤ] e2) ⊗ₜ[ℤ] (s, t)) +
          leftDetection12 (show PairLeft from (e2 ⊗ₜ[ℤ] e1) ⊗ₜ[ℤ] (s, t)) :=
      (leftDetection12).map_add (show PairLeft from (e1 ⊗ₜ[ℤ] e2) ⊗ₜ[ℤ] (s, t))
        (show PairLeft from (e2 ⊗ₜ[ℤ] e1) ⊗ₜ[ℤ] (s, t))
    have hpure : leftDetection12 (show PairLeft from (e1 ⊗ₜ[ℤ] e2) ⊗ₜ[ℤ] (s, t)) +
        leftDetection12 (show PairLeft from (e2 ⊗ₜ[ℤ] e1) ⊗ₜ[ℤ] (s, t)) =
        (p1 e1 * p2 e2) * p1 (s, t) + (p1 e2 * p2 e1) * p1 (s, t) :=
      congrArg₂ (fun x y : ℤ ↦ x + y)
        (leftDetector_tmul p1 p2 p1 e1 e2 (s, t))
        (leftDetector_tmul p1 p2 p1 e2 e1 (s, t))
    exact (congrArg (leftDetection12) hsum).trans
      (hadd.trans (hpure.trans (by simp [p1, p2, e1, e2])))
  have hright12 : rightDetection12 (mixedRight (s, t)) = s := by
    have hadd : rightDetection12 ((show PairRight from e1 ⊗ₜ[ℤ] (e2 ⊗ₜ[ℤ] (s, t))) +
        (show PairRight from e2 ⊗ₜ[ℤ] (e1 ⊗ₜ[ℤ] (s, t)))) =
        rightDetection12 (show PairRight from e1 ⊗ₜ[ℤ] (e2 ⊗ₜ[ℤ] (s, t))) +
          rightDetection12 (show PairRight from e2 ⊗ₜ[ℤ] (e1 ⊗ₜ[ℤ] (s, t))) :=
      (rightDetection12).map_add (show PairRight from e1 ⊗ₜ[ℤ] (e2 ⊗ₜ[ℤ] (s, t)))
        (show PairRight from e2 ⊗ₜ[ℤ] (e1 ⊗ₜ[ℤ] (s, t)))
    have hpure : rightDetection12 (show PairRight from e1 ⊗ₜ[ℤ] (e2 ⊗ₜ[ℤ] (s, t))) +
        rightDetection12 (show PairRight from e2 ⊗ₜ[ℤ] (e1 ⊗ₜ[ℤ] (s, t))) =
        p1 e1 * (p2 e2 * p1 (s, t)) + p1 e2 * (p2 e1 * p1 (s, t)) :=
      congrArg₂ (fun x y : ℤ ↦ x + y)
        (rightDetector_tmul p1 p2 p1 e1 e2 (s, t))
        (rightDetector_tmul p1 p2 p1 e2 e1 (s, t))
    exact hadd.trans (hpure.trans (by simp [p1, p2, e1, e2]))
  have hleft212 : leftDetector p2 p1 p2 (mixedLeft (s, t)) = t := by
    have hadd : leftDetector p2 p1 p2 ((show PairLeft from (e1 ⊗ₜ[ℤ] e2) ⊗ₜ[ℤ] (s, t)) +
        (show PairLeft from (e2 ⊗ₜ[ℤ] e1) ⊗ₜ[ℤ] (s, t))) =
        leftDetector p2 p1 p2 (show PairLeft from (e1 ⊗ₜ[ℤ] e2) ⊗ₜ[ℤ] (s, t)) +
          leftDetector p2 p1 p2 (show PairLeft from (e2 ⊗ₜ[ℤ] e1) ⊗ₜ[ℤ] (s, t)) :=
      (leftDetector p2 p1 p2).map_add (show PairLeft from (e1 ⊗ₜ[ℤ] e2) ⊗ₜ[ℤ] (s, t))
        (show PairLeft from (e2 ⊗ₜ[ℤ] e1) ⊗ₜ[ℤ] (s, t))
    have hpure : leftDetector p2 p1 p2 (show PairLeft from (e1 ⊗ₜ[ℤ] e2) ⊗ₜ[ℤ] (s, t)) +
        leftDetector p2 p1 p2 (show PairLeft from (e2 ⊗ₜ[ℤ] e1) ⊗ₜ[ℤ] (s, t)) =
        (p2 e1 * p1 e2) * p2 (s, t) + (p2 e2 * p1 e1) * p2 (s, t) :=
      congrArg₂ (fun x y : ℤ ↦ x + y)
        (leftDetector_tmul p2 p1 p2 e1 e2 (s, t))
        (leftDetector_tmul p2 p1 p2 e2 e1 (s, t))
    exact (congrArg (leftDetector p2 p1 p2) hsum).trans
      (hadd.trans (hpure.trans (by simp [p1, p2, e1, e2])))
  have hright212 : rightDetector p2 p1 p2 (mixedRight (s, t)) = t := by
    have hadd : rightDetector p2 p1 p2 ((show PairRight from e1 ⊗ₜ[ℤ] (e2 ⊗ₜ[ℤ] (s, t))) +
        (show PairRight from e2 ⊗ₜ[ℤ] (e1 ⊗ₜ[ℤ] (s, t)))) =
        rightDetector p2 p1 p2 (show PairRight from e1 ⊗ₜ[ℤ] (e2 ⊗ₜ[ℤ] (s, t))) +
          rightDetector p2 p1 p2 (show PairRight from e2 ⊗ₜ[ℤ] (e1 ⊗ₜ[ℤ] (s, t))) :=
      (rightDetector p2 p1 p2).map_add (show PairRight from e1 ⊗ₜ[ℤ] (e2 ⊗ₜ[ℤ] (s, t)))
        (show PairRight from e2 ⊗ₜ[ℤ] (e1 ⊗ₜ[ℤ] (s, t)))
    have hpure : rightDetector p2 p1 p2 (show PairRight from e1 ⊗ₜ[ℤ] (e2 ⊗ₜ[ℤ] (s, t))) +
        rightDetector p2 p1 p2 (show PairRight from e2 ⊗ₜ[ℤ] (e1 ⊗ₜ[ℤ] (s, t))) =
        p2 e1 * (p1 e2 * p2 (s, t)) + p2 e2 * (p1 e1 * p2 (s, t)) :=
      congrArg₂ (fun x y : ℤ ↦ x + y)
        (rightDetector_tmul p2 p1 p2 e1 e2 (s, t))
        (rightDetector_tmul p2 p1 p2 e2 e1 (s, t))
    exact hadd.trans (hpure.trans (by simp [p1, p2, e1, e2]))
  exact ⟨hforward, hleft12, hright12, hleft212, hright212⟩

/-- Doubling an algebraic coefficient vector. -/
noncomputable def coefficientDoubling : integerPairCoefficients →ₗ[ℤ] integerPairCoefficients :=
  (2 : ℤ) • LinearMap.id

/-- Swapping the two algebraic coefficient coordinates. -/
noncomputable def coefficientSwap : integerPairCoefficients →ₗ[ℤ] integerPairCoefficients :=
  (LinearEquiv.prodComm ℤ ℤ ℤ).toLinearMap

/-- Joint-action continuity gives continuous scalar doubling on the right factor. -/
noncomputable def rightDoubling : integerPairModule →L[ℤ] integerPairModule :=
  (2 : ℤ) • ContinuousLinearMap.id ℤ integerPairModule

/-- Map both algebraic coefficient factors by `f` and `g` and the supplied
right factor by `h` on the left-parenthesized tensor. -/
noncomputable def flatMap
    (f g : integerPairCoefficients →ₗ[ℤ] integerPairCoefficients)
    (h : integerPairModule →L[ℤ] integerPairModule) : PairLeft →L[ℤ] PairLeft :=
  TopModuleCat.tensorMapCLM ℤ
    (C := ModuleCat.of ℤ (integerPairCoefficients ⊗[ℤ] integerPairCoefficients))
    (D := ModuleCat.of ℤ (integerPairCoefficients ⊗[ℤ] integerPairCoefficients))
    (TensorProduct.map f g) h

/-- Map the three factors by `f`, `g` and `h` on the right-parenthesized tensor,
using the canonical continuous tensor map at each nesting level. -/
noncomputable def nestedMap
    (f g : integerPairCoefficients →ₗ[ℤ] integerPairCoefficients)
    (h : integerPairModule →L[ℤ] integerPairModule) : PairRight →L[ℤ] PairRight :=
  TopModuleCat.tensorMapCLM ℤ f (TopModuleCat.tensorMapCLM ℤ g h)

/-- First map the three factors on the flat side, then reassociate. -/
noncomputable def flatThenAssoc
    (f g : integerPairCoefficients →ₗ[ℤ] integerPairCoefficients)
    (h : integerPairModule →L[ℤ] integerPairModule) : PairLeft →L[ℤ] PairRight :=
  integerPairAssoc.toContinuousLinearMap.comp (flatMap f g h)

/-- Evaluate mapping followed by reassociation on an arbitrary tensor. -/
@[simp]
theorem flatThenAssoc_apply
    (f g : integerPairCoefficients →ₗ[ℤ] integerPairCoefficients)
    (h : integerPairModule →L[ℤ] integerPairModule) (x : PairLeft) :
    flatThenAssoc f g h x = integerPairAssoc (flatMap f g h x) := rfl

/-- First reassociate, then map the three factors on the nested side. -/
noncomputable def assocThenNested
    (f g : integerPairCoefficients →ₗ[ℤ] integerPairCoefficients)
    (h : integerPairModule →L[ℤ] integerPairModule) : PairLeft →L[ℤ] PairRight :=
  (nestedMap f g h).comp integerPairAssoc.toContinuousLinearMap

/-- The identity linear map on the rank-two integer coefficient module. -/
abbrev coefficientId : integerPairCoefficients →ₗ[ℤ] integerPairCoefficients :=
  LinearMap.id
/-- The identity continuous linear map on the supplied rank-two right factor. -/
noncomputable def rightId : integerPairModule →L[ℤ] integerPairModule :=
  ContinuousLinearMap.id ℤ integerPairModule

/-- Right doubling changes the detected value from one to two, both naturality
frames agree, and inverse reassociation recovers the doubled flat tensor. -/
theorem integerPair_right_doubling :
    flatThenAssoc coefficientId coefficientId rightDoubling =
        assocThenNested coefficientId coefficientId rightDoubling ∧
      flatThenAssoc coefficientId coefficientId rightDoubling leftTriple =
        e1 ⊗ₜ[ℤ] (e2 ⊗ₜ[ℤ] ((2 : ℤ) • e1)) ∧
      rightDetection12 (flatThenAssoc coefficientId coefficientId rightDoubling leftTriple) = 2 ∧
      rightDetection12 (assocThenNested coefficientId coefficientId rightDoubling leftTriple) = 2 ∧
      flatMap coefficientId coefficientId rightDoubling leftTriple ≠ leftTriple ∧
      integerPairAssoc.symm
          (assocThenNested coefficientId coefficientId rightDoubling leftTriple) =
        flatMap coefficientId coefficientId rightDoubling leftTriple := by
  have hnat : flatThenAssoc coefficientId coefficientId rightDoubling =
      assocThenNested coefficientId coefficientId rightDoubling := by
    exact (TopModuleCat.tensorAssocContinuousLinearEquiv_naturality ℤ
      integerPairCoefficients integerPairCoefficients integerPairModule
      coefficientId coefficientId rightDoubling).symm
  have hflat : flatMap coefficientId coefficientId rightDoubling leftTriple =
      (e1 ⊗ₜ[ℤ] e2) ⊗ₜ[ℤ] ((2 : ℤ) • e1) := by
    have hmap : flatMap coefficientId coefficientId rightDoubling leftTriple =
        (show PairLeft from
          TensorProduct.map (TensorProduct.map coefficientId coefficientId)
            rightDoubling.toLinearMap ((e1 ⊗ₜ[ℤ] e2) ⊗ₜ[ℤ] e1)) :=
      TopModuleCat.tensorMapCLM_apply ℤ
        (C := ModuleCat.of ℤ (integerPairCoefficients ⊗[ℤ] integerPairCoefficients))
        (D := ModuleCat.of ℤ (integerPairCoefficients ⊗[ℤ] integerPairCoefficients))
        (M := integerPairModule) (N := integerPairModule)
        (TensorProduct.map coefficientId coefficientId) rightDoubling
        (show PairLeft from (e1 ⊗ₜ[ℤ] e2) ⊗ₜ[ℤ] e1)
    have hpure : (show PairLeft from
        TensorProduct.map (TensorProduct.map coefficientId coefficientId) rightDoubling.toLinearMap
          ((e1 ⊗ₜ[ℤ] e2) ⊗ₜ[ℤ] e1)) =
        (show PairLeft from ((TensorProduct.map coefficientId coefficientId) (e1 ⊗ₜ[ℤ] e2)) ⊗ₜ[ℤ]
          rightDoubling e1) :=
      TensorProduct.map_tmul (TensorProduct.map coefficientId coefficientId)
        rightDoubling.toLinearMap
        (show ModuleCat.of ℤ (integerPairCoefficients ⊗[ℤ] integerPairCoefficients) from
          e1 ⊗ₜ[ℤ] e2)
        (show integerPairModule from e1)
    have hcoeff : (show ModuleCat.of ℤ (integerPairCoefficients ⊗[ℤ] integerPairCoefficients) from
        (TensorProduct.map coefficientId coefficientId) (e1 ⊗ₜ[ℤ] e2)) =
        (show ModuleCat.of ℤ (integerPairCoefficients ⊗[ℤ] integerPairCoefficients) from
          e1 ⊗ₜ[ℤ] e2) :=
      (TensorProduct.map_tmul coefficientId coefficientId e1 e2).trans
        (by simp only [coefficientId, LinearMap.id_apply])
    have hright : rightDoubling e1 = ((2 : ℤ) • e1) := by
      simp only [rightDoubling, smul_apply, ContinuousLinearMap.id_apply]
    exact hmap.trans (hpure.trans
      (congrArg₂ (fun (z : ModuleCat.of ℤ
          (integerPairCoefficients ⊗[ℤ] integerPairCoefficients)) (m : integerPairModule) ↦
        (show PairLeft from z ⊗ₜ[ℤ] m)) hcoeff hright))
  have hvalue : flatThenAssoc coefficientId coefficientId rightDoubling leftTriple =
      e1 ⊗ₜ[ℤ] (e2 ⊗ₜ[ℤ] ((2 : ℤ) • e1)) := by
    rw [flatThenAssoc_apply, hflat]
    change (TopModuleCat.tensorAssocContinuousLinearEquiv ℤ
        integerPairCoefficients integerPairCoefficients integerPairModule)
        (show TopModuleCat.tensorLeftObj ℤ
            (ModuleCat.of ℤ (integerPairCoefficients ⊗[ℤ] integerPairCoefficients))
            integerPairModule from
          (e1 ⊗ₜ[ℤ] e2) ⊗ₜ[ℤ] ((2 : ℤ) • e1)) =
        (show TopModuleCat.tensorLeftObj ℤ integerPairCoefficients
            (TopModuleCat.tensorLeftObj ℤ integerPairCoefficients integerPairModule) from
          e1 ⊗ₜ[ℤ] (e2 ⊗ₜ[ℤ] ((2 : ℤ) • e1)))
    exact (TopModuleCat.tensorAssocContinuousLinearEquiv_apply ℤ
      integerPairCoefficients integerPairCoefficients integerPairModule _).trans
        (TensorProduct.assoc_tmul (R := ℤ) e1 e2 ((2 : ℤ) • e1))
  have hdetect : rightDetection12
      (flatThenAssoc coefficientId coefficientId rightDoubling leftTriple) = 2 := by
    have hpure : rightDetection12 (show PairRight from e1 ⊗ₜ[ℤ] (e2 ⊗ₜ[ℤ] ((2 : ℤ) • e1))) = 2 :=
      (rightDetector_tmul p1 p2 p1 e1 e2 ((2 : ℤ) • e1)).trans
        (by norm_num [p1, p2, e1, e2])
    exact (congrArg rightDetection12 hvalue).trans hpure
  have hflatDetect : leftDetection12
      (flatMap coefficientId coefficientId rightDoubling leftTriple) = 2 := by
    have hpure : leftDetection12 (show PairLeft from (e1 ⊗ₜ[ℤ] e2) ⊗ₜ[ℤ] ((2 : ℤ) • e1)) = 2 :=
      (leftDetector_tmul p1 p2 p1 e1 e2 ((2 : ℤ) • e1)).trans
        (by norm_num [p1, p2, e1, e2])
    exact (congrArg leftDetection12 hflat).trans hpure
  refine ⟨hnat, hvalue, hdetect, ?_, ?_, ?_⟩
  · rw [← hnat]
    exact hdetect
  · intro h
    have hdet := congrArg leftDetection12 h
    rw [hflatDetect, integerPair_nonzero.1] at hdet
    norm_num at hdet
  · rw [← hnat]
    exact integerPairAssoc.symm_apply_apply
      (flatMap coefficientId coefficientId rightDoubling leftTriple)

/-- Doubling the first algebraic coefficient also changes the detected value
from one to two and satisfies the same all-factor naturality diagram. -/
theorem integerPair_coefficient_doubling :
    flatThenAssoc coefficientDoubling coefficientId rightId =
        assocThenNested coefficientDoubling coefficientId rightId ∧
      rightDetection12 (flatThenAssoc coefficientDoubling coefficientId rightId leftTriple) = 2 ∧
      rightDetection12 (assocThenNested coefficientDoubling coefficientId rightId leftTriple) = 2 ∧
      flatMap coefficientDoubling coefficientId rightId leftTriple ≠ leftTriple := by
  have hnat : flatThenAssoc coefficientDoubling coefficientId rightId =
      assocThenNested coefficientDoubling coefficientId rightId := by
    exact (TopModuleCat.tensorAssocContinuousLinearEquiv_naturality ℤ
      integerPairCoefficients integerPairCoefficients integerPairModule
      coefficientDoubling coefficientId rightId).symm
  have hflat : flatMap coefficientDoubling coefficientId rightId leftTriple =
      (((2 : ℤ) • e1) ⊗ₜ[ℤ] e2) ⊗ₜ[ℤ] e1 := by
    have hmap : flatMap coefficientDoubling coefficientId rightId leftTriple =
        (show PairLeft from
          TensorProduct.map (TensorProduct.map coefficientDoubling coefficientId)
            rightId.toLinearMap ((e1 ⊗ₜ[ℤ] e2) ⊗ₜ[ℤ] e1)) :=
      TopModuleCat.tensorMapCLM_apply ℤ
        (C := ModuleCat.of ℤ (integerPairCoefficients ⊗[ℤ] integerPairCoefficients))
        (D := ModuleCat.of ℤ (integerPairCoefficients ⊗[ℤ] integerPairCoefficients))
        (M := integerPairModule) (N := integerPairModule)
        (TensorProduct.map coefficientDoubling coefficientId) rightId
        (show PairLeft from (e1 ⊗ₜ[ℤ] e2) ⊗ₜ[ℤ] e1)
    have hpure : (show PairLeft from
        TensorProduct.map (TensorProduct.map coefficientDoubling coefficientId) rightId.toLinearMap
          ((e1 ⊗ₜ[ℤ] e2) ⊗ₜ[ℤ] e1)) =
        (show PairLeft from ((TensorProduct.map coefficientDoubling coefficientId) (e1 ⊗ₜ[ℤ] e2))
          ⊗ₜ[ℤ] rightId e1) :=
      TensorProduct.map_tmul (TensorProduct.map coefficientDoubling coefficientId)
        rightId.toLinearMap
        (show ModuleCat.of ℤ (integerPairCoefficients ⊗[ℤ] integerPairCoefficients) from
          e1 ⊗ₜ[ℤ] e2)
        (show integerPairModule from e1)
    have hcoeff : (show ModuleCat.of ℤ (integerPairCoefficients ⊗[ℤ] integerPairCoefficients) from
        (TensorProduct.map coefficientDoubling coefficientId) (e1 ⊗ₜ[ℤ] e2)) =
        (show ModuleCat.of ℤ (integerPairCoefficients ⊗[ℤ] integerPairCoefficients) from
          ((2 : ℤ) • e1) ⊗ₜ[ℤ] e2) :=
      (TensorProduct.map_tmul coefficientDoubling coefficientId e1 e2).trans
        (by simp only [coefficientDoubling, coefficientId, LinearMap.smul_apply,
          LinearMap.id_apply])
    have hright : rightId e1 = e1 := by
      simp only [rightId, ContinuousLinearMap.id_apply]
    exact hmap.trans (hpure.trans
      (congrArg₂ (fun (z : ModuleCat.of ℤ
          (integerPairCoefficients ⊗[ℤ] integerPairCoefficients)) (m : integerPairModule) ↦
        (show PairLeft from z ⊗ₜ[ℤ] m)) hcoeff hright))
  have hvalue : flatThenAssoc coefficientDoubling coefficientId rightId leftTriple =
      ((2 : ℤ) • e1) ⊗ₜ[ℤ] (e2 ⊗ₜ[ℤ] e1) := by
    rw [flatThenAssoc_apply, hflat]
    change (TopModuleCat.tensorAssocContinuousLinearEquiv ℤ
        integerPairCoefficients integerPairCoefficients integerPairModule)
        (show TopModuleCat.tensorLeftObj ℤ
            (ModuleCat.of ℤ (integerPairCoefficients ⊗[ℤ] integerPairCoefficients))
            integerPairModule from
          (((2 : ℤ) • e1) ⊗ₜ[ℤ] e2) ⊗ₜ[ℤ] e1) =
        (show TopModuleCat.tensorLeftObj ℤ integerPairCoefficients
            (TopModuleCat.tensorLeftObj ℤ integerPairCoefficients integerPairModule) from
          ((2 : ℤ) • e1) ⊗ₜ[ℤ] (e2 ⊗ₜ[ℤ] e1))
    exact (TopModuleCat.tensorAssocContinuousLinearEquiv_apply ℤ
      integerPairCoefficients integerPairCoefficients integerPairModule _).trans
        (TensorProduct.assoc_tmul (R := ℤ) ((2 : ℤ) • e1) e2 e1)
  have hdetect : rightDetection12
      (flatThenAssoc coefficientDoubling coefficientId rightId leftTriple) = 2 := by
    have hpure : rightDetection12 (show PairRight from ((2 : ℤ) • e1) ⊗ₜ[ℤ] (e2 ⊗ₜ[ℤ] e1)) = 2 :=
      (rightDetector_tmul p1 p2 p1 ((2 : ℤ) • e1) e2 e1).trans
        (by norm_num [p1, p2, e1, e2])
    exact (congrArg rightDetection12 hvalue).trans hpure
  have hflatDetect : leftDetection12
      (flatMap coefficientDoubling coefficientId rightId leftTriple) = 2 := by
    have hpure : leftDetection12 (show PairLeft from (((2 : ℤ) • e1) ⊗ₜ[ℤ] e2) ⊗ₜ[ℤ] e1) = 2 :=
      (leftDetector_tmul p1 p2 p1 ((2 : ℤ) • e1) e2 e1).trans
        (by norm_num [p1, p2, e1, e2])
    exact (congrArg leftDetection12 hflat).trans hpure
  refine ⟨hnat, hdetect, ?_, ?_⟩
  · rw [← hnat]
    exact hdetect
  · intro h
    have hdet := congrArg leftDetection12 h
    rw [hflatDetect, integerPair_nonzero.1] at hdet
    norm_num at hdet

/-- Both coefficient swaps and right doubling are active: the endpoint has the
opposite coefficient directions and is detected by the other detector as two. -/
theorem integerPair_both_coefficients :
    flatThenAssoc coefficientSwap coefficientSwap rightDoubling =
        assocThenNested coefficientSwap coefficientSwap rightDoubling ∧
      flatThenAssoc coefficientSwap coefficientSwap rightDoubling leftTriple =
        e2 ⊗ₜ[ℤ] (e1 ⊗ₜ[ℤ] ((2 : ℤ) • e1)) ∧
      rightDetection21
          (flatThenAssoc coefficientSwap coefficientSwap rightDoubling leftTriple) = 2 ∧
      rightDetection21
          (assocThenNested coefficientSwap coefficientSwap rightDoubling leftTriple) = 2 := by
  have hnat : flatThenAssoc coefficientSwap coefficientSwap rightDoubling =
      assocThenNested coefficientSwap coefficientSwap rightDoubling := by
    exact (TopModuleCat.tensorAssocContinuousLinearEquiv_naturality ℤ
      integerPairCoefficients integerPairCoefficients integerPairModule
      coefficientSwap coefficientSwap rightDoubling).symm
  have hflat : flatMap coefficientSwap coefficientSwap rightDoubling leftTriple =
      (e2 ⊗ₜ[ℤ] e1) ⊗ₜ[ℤ] ((2 : ℤ) • e1) := by
    have hmap : flatMap coefficientSwap coefficientSwap rightDoubling leftTriple =
        (show PairLeft from
          TensorProduct.map (TensorProduct.map coefficientSwap coefficientSwap)
            rightDoubling.toLinearMap ((e1 ⊗ₜ[ℤ] e2) ⊗ₜ[ℤ] e1)) :=
      TopModuleCat.tensorMapCLM_apply ℤ
        (C := ModuleCat.of ℤ (integerPairCoefficients ⊗[ℤ] integerPairCoefficients))
        (D := ModuleCat.of ℤ (integerPairCoefficients ⊗[ℤ] integerPairCoefficients))
        (M := integerPairModule) (N := integerPairModule)
        (TensorProduct.map coefficientSwap coefficientSwap) rightDoubling
        (show PairLeft from (e1 ⊗ₜ[ℤ] e2) ⊗ₜ[ℤ] e1)
    have hpure : (show PairLeft from
        TensorProduct.map (TensorProduct.map coefficientSwap coefficientSwap)
          rightDoubling.toLinearMap ((e1 ⊗ₜ[ℤ] e2) ⊗ₜ[ℤ] e1)) =
        (show PairLeft from ((TensorProduct.map coefficientSwap coefficientSwap) (e1 ⊗ₜ[ℤ] e2))
          ⊗ₜ[ℤ] rightDoubling e1) :=
      TensorProduct.map_tmul (TensorProduct.map coefficientSwap coefficientSwap)
        rightDoubling.toLinearMap
        (show ModuleCat.of ℤ (integerPairCoefficients ⊗[ℤ] integerPairCoefficients) from
          e1 ⊗ₜ[ℤ] e2)
        (show integerPairModule from e1)
    have hcoeff : (show ModuleCat.of ℤ (integerPairCoefficients ⊗[ℤ] integerPairCoefficients) from
        (TensorProduct.map coefficientSwap coefficientSwap) (e1 ⊗ₜ[ℤ] e2)) =
        (show ModuleCat.of ℤ (integerPairCoefficients ⊗[ℤ] integerPairCoefficients) from
          e2 ⊗ₜ[ℤ] e1) :=
      (TensorProduct.map_tmul coefficientSwap coefficientSwap e1 e2).trans
        (by simp [coefficientSwap, e1, e2])
    have hright : rightDoubling e1 = ((2 : ℤ) • e1) := by
      simp only [rightDoubling, smul_apply, ContinuousLinearMap.id_apply]
    exact hmap.trans (hpure.trans
      (congrArg₂ (fun (z : ModuleCat.of ℤ
          (integerPairCoefficients ⊗[ℤ] integerPairCoefficients)) (m : integerPairModule) ↦
        (show PairLeft from z ⊗ₜ[ℤ] m)) hcoeff hright))
  have hvalue : flatThenAssoc coefficientSwap coefficientSwap rightDoubling leftTriple =
      e2 ⊗ₜ[ℤ] (e1 ⊗ₜ[ℤ] ((2 : ℤ) • e1)) := by
    rw [flatThenAssoc_apply, hflat]
    change (TopModuleCat.tensorAssocContinuousLinearEquiv ℤ
        integerPairCoefficients integerPairCoefficients integerPairModule)
        (show TopModuleCat.tensorLeftObj ℤ
            (ModuleCat.of ℤ (integerPairCoefficients ⊗[ℤ] integerPairCoefficients))
            integerPairModule from
          (e2 ⊗ₜ[ℤ] e1) ⊗ₜ[ℤ] ((2 : ℤ) • e1)) =
        (show TopModuleCat.tensorLeftObj ℤ integerPairCoefficients
            (TopModuleCat.tensorLeftObj ℤ integerPairCoefficients integerPairModule) from
          e2 ⊗ₜ[ℤ] (e1 ⊗ₜ[ℤ] ((2 : ℤ) • e1)))
    exact (TopModuleCat.tensorAssocContinuousLinearEquiv_apply ℤ
      integerPairCoefficients integerPairCoefficients integerPairModule _).trans
        (TensorProduct.assoc_tmul (R := ℤ) e2 e1 ((2 : ℤ) • e1))
  have hdetect : rightDetection21
      (flatThenAssoc coefficientSwap coefficientSwap rightDoubling leftTriple) = 2 := by
    have hpure : rightDetection21 (show PairRight from e2 ⊗ₜ[ℤ] (e1 ⊗ₜ[ℤ] ((2 : ℤ) • e1))) = 2 :=
      (rightDetector_tmul p2 p1 p1 e2 e1 ((2 : ℤ) • e1)).trans
        (by norm_num [p1, p2, e1, e2])
    exact (congrArg rightDetection21 hvalue).trans hpure
  refine ⟨hnat, hvalue, hdetect, ?_⟩
  rw [← hnat]
  exact hdetect

/-- Commute the two factors of the flat coefficient tensor, leaving the
continuous right factor unchanged. -/
noncomputable def flatCoefficientSwap : PairLeft →L[ℤ] PairLeft :=
  TopModuleCat.tensorMapCLM ℤ
    (C := ModuleCat.of ℤ (integerPairCoefficients ⊗[ℤ] integerPairCoefficients))
    (D := ModuleCat.of ℤ (integerPairCoefficients ⊗[ℤ] integerPairCoefficients))
    (TensorProduct.comm ℤ integerPairCoefficients integerPairCoefficients).toLinearMap rightId

/-- Flat coefficient commutation changes the first detector from one to zero,
while the second detector observes the swapped nonzero component. -/
theorem integerPair_flat_swap :
    flatCoefficientSwap leftTriple = (e2 ⊗ₜ[ℤ] e1) ⊗ₜ[ℤ] e1 ∧
      leftDetection12 (flatCoefficientSwap leftTriple) = 0 ∧
      rightDetection12 (integerPairAssoc (flatCoefficientSwap leftTriple)) = 0 ∧
      rightDetection21 (integerPairAssoc (flatCoefficientSwap leftTriple)) = 1 ∧
      flatCoefficientSwap leftTriple ≠ leftTriple := by
  have hswap : flatCoefficientSwap leftTriple =
      (e2 ⊗ₜ[ℤ] e1) ⊗ₜ[ℤ] e1 := by
    have hmap : flatCoefficientSwap leftTriple =
        (show PairLeft from
          TensorProduct.map (TensorProduct.comm ℤ integerPairCoefficients
            integerPairCoefficients).toLinearMap rightId.toLinearMap ((e1 ⊗ₜ[ℤ] e2) ⊗ₜ[ℤ] e1)) :=
      TopModuleCat.tensorMapCLM_apply ℤ
        (C := ModuleCat.of ℤ (integerPairCoefficients ⊗[ℤ] integerPairCoefficients))
        (D := ModuleCat.of ℤ (integerPairCoefficients ⊗[ℤ] integerPairCoefficients))
        (M := integerPairModule) (N := integerPairModule)
        (TensorProduct.comm ℤ integerPairCoefficients integerPairCoefficients).toLinearMap rightId
        (show PairLeft from (e1 ⊗ₜ[ℤ] e2) ⊗ₜ[ℤ] e1)
    have hpure : (show PairLeft from
        TensorProduct.map (TensorProduct.comm ℤ integerPairCoefficients
          integerPairCoefficients).toLinearMap rightId.toLinearMap ((e1 ⊗ₜ[ℤ] e2) ⊗ₜ[ℤ] e1)) =
        (show PairLeft from ((TensorProduct.comm ℤ integerPairCoefficients
          integerPairCoefficients).toLinearMap (e1 ⊗ₜ[ℤ] e2)) ⊗ₜ[ℤ] rightId e1) :=
      TensorProduct.map_tmul (TensorProduct.comm ℤ integerPairCoefficients
        integerPairCoefficients).toLinearMap rightId.toLinearMap
        (show ModuleCat.of ℤ (integerPairCoefficients ⊗[ℤ] integerPairCoefficients) from
          e1 ⊗ₜ[ℤ] e2)
        (show integerPairModule from e1)
    have hcoeff : (show ModuleCat.of ℤ (integerPairCoefficients ⊗[ℤ] integerPairCoefficients) from
        (TensorProduct.comm ℤ integerPairCoefficients integerPairCoefficients).toLinearMap
          (e1 ⊗ₜ[ℤ] e2)) =
        (show ModuleCat.of ℤ (integerPairCoefficients ⊗[ℤ] integerPairCoefficients) from
          e2 ⊗ₜ[ℤ] e1) :=
      TensorProduct.comm_tmul ℤ integerPairCoefficients integerPairCoefficients e1 e2
    have hright : rightId e1 = e1 := by
      simp only [rightId, ContinuousLinearMap.id_apply]
    exact hmap.trans (hpure.trans
      (congrArg₂ (fun (z : ModuleCat.of ℤ
          (integerPairCoefficients ⊗[ℤ] integerPairCoefficients)) (m : integerPairModule) ↦
        (show PairLeft from z ⊗ₜ[ℤ] m)) hcoeff hright))
  have hvalue : integerPairAssoc (flatCoefficientSwap leftTriple) =
      e2 ⊗ₜ[ℤ] (e1 ⊗ₜ[ℤ] e1) := by
    rw [hswap]
    change (TopModuleCat.tensorAssocContinuousLinearEquiv ℤ
        integerPairCoefficients integerPairCoefficients integerPairModule)
        (show TopModuleCat.tensorLeftObj ℤ
            (ModuleCat.of ℤ (integerPairCoefficients ⊗[ℤ] integerPairCoefficients))
            integerPairModule from
          (e2 ⊗ₜ[ℤ] e1) ⊗ₜ[ℤ] e1) =
        (show TopModuleCat.tensorLeftObj ℤ integerPairCoefficients
            (TopModuleCat.tensorLeftObj ℤ integerPairCoefficients integerPairModule) from
          e2 ⊗ₜ[ℤ] (e1 ⊗ₜ[ℤ] e1))
    exact (TopModuleCat.tensorAssocContinuousLinearEquiv_apply ℤ
      integerPairCoefficients integerPairCoefficients integerPairModule _).trans
        (TensorProduct.assoc_tmul (R := ℤ) e2 e1 e1)
  have hleft : leftDetection12 (flatCoefficientSwap leftTriple) = 0 := by
    have hpure : leftDetection12 (show PairLeft from (e2 ⊗ₜ[ℤ] e1) ⊗ₜ[ℤ] e1) = 0 :=
      (leftDetector_tmul p1 p2 p1 e2 e1 e1).trans
        (by norm_num [p1, p2, e1, e2])
    exact (congrArg leftDetection12 hswap).trans hpure
  refine ⟨hswap, hleft, ?_, ?_, ?_⟩
  · have hpure : rightDetection12 (show PairRight from e2 ⊗ₜ[ℤ] (e1 ⊗ₜ[ℤ] e1)) = 0 :=
      (rightDetector_tmul p1 p2 p1 e2 e1 e1).trans (by norm_num [p1, p2, e1, e2])
    exact (congrArg rightDetection12 hvalue).trans hpure
  · have hpure : rightDetection21 (show PairRight from e2 ⊗ₜ[ℤ] (e1 ⊗ₜ[ℤ] e1)) = 1 :=
      (rightDetector_tmul p2 p1 p1 e2 e1 e1).trans (by norm_num [p1, p2, e1, e2])
    exact (congrArg rightDetection21 hvalue).trans hpure
  · intro h
    have hdet := congrArg leftDetection12 h
    rw [hleft, integerPair_nonzero.1] at hdet
    norm_num at hdet

/-- The nonfree coefficient module over the integers. -/
abbrev torsionCoefficients : ModuleCat ℤ := ModuleCat.of ℤ (ZMod 3)

/-- The finite discrete torsion module as the supplied right factor. -/
abbrev torsionModule : TopModuleCat ℤ := TopModuleCat.of ℤ (ZMod 3)

/-- The integer-pair and torsion right factors have discrete supplied topologies,
continuous addition and joint integer scalar action. -/
theorem discrete_right_modules :
    DiscreteTopology (ℤ × ℤ) ∧ ContinuousAdd (ℤ × ℤ) ∧ ContinuousSMul ℤ (ℤ × ℤ) ∧
      DiscreteTopology (ZMod 3) ∧ ContinuousAdd (ZMod 3) ∧ ContinuousSMul ℤ (ZMod 3) := by
  exact ⟨inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance⟩

/-- The left-parenthesized tensor of three copies of `ZMod 3` over the integers,
with the supplied discrete topology on the right factor. -/
noncomputable abbrev TorsionLeft := TopModuleCat.tensorLeftObj ℤ
  (ModuleCat.of ℤ (torsionCoefficients ⊗[ℤ] torsionCoefficients)) torsionModule
/-- The right-parenthesized tensor of three integer torsion modules `ZMod 3`,
using the one-sided tensor topology at both nesting levels. -/
noncomputable abbrev TorsionRight := TopModuleCat.tensorLeftObj ℤ torsionCoefficients
  (TopModuleCat.tensorLeftObj ℤ torsionCoefficients torsionModule)

/-- Reassociation with three integer torsion modules. -/
noncomputable def torsionAssoc : TorsionLeft ≃L[ℤ] TorsionRight :=
  TopModuleCat.tensorAssocContinuousLinearEquiv ℤ
    torsionCoefficients torsionCoefficients torsionModule

/-- The flat triple of ones in the torsion modules. -/
noncomputable def torsionLeftTriple : TorsionLeft :=
  ((1 : ZMod 3) ⊗ₜ[ℤ] (1 : ZMod 3)) ⊗ₜ[ℤ] (1 : ZMod 3)

/-- The nested triple of ones in the torsion modules. -/
noncomputable def torsionRightTriple : TorsionRight :=
  (1 : ZMod 3) ⊗ₜ[ℤ] ((1 : ZMod 3) ⊗ₜ[ℤ] (1 : ZMod 3))

/-- Integer-balanced multiplication detects the flat torsion triple. -/
noncomputable def torsionLeftDetector : TorsionLeft →ₗ[ℤ] ZMod 3 :=
  TensorProduct.lift ((LinearMap.mul ℤ (ZMod 3)).compl₁₂
    (TensorProduct.lift (LinearMap.mul ℤ (ZMod 3))) (LinearMap.id : ZMod 3 →ₗ[ℤ] ZMod 3))

/-- Integer-balanced multiplication detects the nested torsion triple. -/
noncomputable def torsionRightDetector : TorsionRight →ₗ[ℤ] ZMod 3 :=
  TensorProduct.lift ((LinearMap.mul ℤ (ZMod 3)).compl₁₂
    (LinearMap.id : ZMod 3 →ₗ[ℤ] ZMod 3) (TensorProduct.lift (LinearMap.mul ℤ (ZMod 3))))

/-- The torsion coefficients are nonfree over the nonfield scalar ring, but the
triple tensors are nonzero and transported in both directions. -/
theorem torsion_nonfree_nonzero :
    ¬ Module.Free ℤ (ZMod 3) ∧ (3 : ℤ) • (1 : ZMod 3) = 0 ∧
      torsionLeftDetector torsionLeftTriple = 1 ∧ torsionRightDetector torsionRightTriple = 1 ∧
      torsionLeftTriple ≠ 0 ∧ torsionRightTriple ≠ 0 ∧
      torsionAssoc torsionLeftTriple = torsionRightTriple ∧
      torsionAssoc.symm torsionRightTriple = torsionLeftTriple := by
  have hscalar : (3 : ℤ) • (1 : ZMod 3) = 0 := by decide
  have hnonfree : ¬ Module.Free ℤ (ZMod 3) := by
    intro hfree
    let : Module.Free ℤ (ZMod 3) := hfree
    have hone : (1 : ZMod 3) = 0 :=
      (smul_eq_zero.mp hscalar).resolve_left (by decide : (3 : ℤ) ≠ 0)
    exact one_ne_zero hone
  have hleft : torsionLeftDetector torsionLeftTriple = 1 := by
    calc
      torsionLeftDetector torsionLeftTriple =
          (LinearMap.mul ℤ (ZMod 3)).compl₁₂
            (TensorProduct.lift (LinearMap.mul ℤ (ZMod 3)))
            (LinearMap.id : ZMod 3 →ₗ[ℤ] ZMod 3)
            ((1 : ZMod 3) ⊗ₜ[ℤ] (1 : ZMod 3)) (1 : ZMod 3) :=
        TensorProduct.lift.tmul
          (f' := (LinearMap.mul ℤ (ZMod 3)).compl₁₂
            (TensorProduct.lift (LinearMap.mul ℤ (ZMod 3)))
            (LinearMap.id : ZMod 3 →ₗ[ℤ] ZMod 3))
          ((1 : ZMod 3) ⊗ₜ[ℤ] (1 : ZMod 3)) (1 : ZMod 3)
      _ = 1 := by
        rw [LinearMap.compl₁₂_apply, LinearMap.mul_apply',
          TensorProduct.lift.tmul (f' := LinearMap.mul ℤ (ZMod 3))
            (1 : ZMod 3) (1 : ZMod 3), LinearMap.mul_apply']
        simp only [LinearMap.id_apply, mul_one]
  have hright : torsionRightDetector torsionRightTriple = 1 := by
    calc
      torsionRightDetector torsionRightTriple =
          (LinearMap.mul ℤ (ZMod 3)).compl₁₂
            (LinearMap.id : ZMod 3 →ₗ[ℤ] ZMod 3)
            (TensorProduct.lift (LinearMap.mul ℤ (ZMod 3)))
            (1 : ZMod 3) ((1 : ZMod 3) ⊗ₜ[ℤ] (1 : ZMod 3)) :=
        TensorProduct.lift.tmul
          (f' := (LinearMap.mul ℤ (ZMod 3)).compl₁₂
            (LinearMap.id : ZMod 3 →ₗ[ℤ] ZMod 3)
            (TensorProduct.lift (LinearMap.mul ℤ (ZMod 3))))
          (1 : ZMod 3) ((1 : ZMod 3) ⊗ₜ[ℤ] (1 : ZMod 3))
      _ = 1 := by
        rw [LinearMap.compl₁₂_apply, LinearMap.mul_apply',
          TensorProduct.lift.tmul (f' := LinearMap.mul ℤ (ZMod 3))
            (1 : ZMod 3) (1 : ZMod 3), LinearMap.mul_apply']
        simp only [LinearMap.id_apply, mul_one]
  refine ⟨hnonfree, hscalar, hleft, hright, ?_, ?_, ?_, ?_⟩
  · intro h
    have hzero : (1 : ZMod 3) = 0 := hleft.symm.trans (by rw [h, map_zero])
    exact one_ne_zero hzero
  · intro h
    have hzero : (1 : ZMod 3) = 0 := hright.symm.trans (by rw [h, map_zero])
    exact one_ne_zero hzero
  · exact TopModuleCat.tensorAssocContinuousLinearEquiv_tmul ℤ
      torsionCoefficients torsionCoefficients torsionModule
      (1 : ZMod 3) (1 : ZMod 3) (1 : ZMod 3)
  · exact TopModuleCat.tensorAssocContinuousLinearEquiv_symm_tmul ℤ
      torsionCoefficients torsionCoefficients torsionModule
      (1 : ZMod 3) (1 : ZMod 3) (1 : ZMod 3)

/-- The singleton zero integer coefficient module of functions `Fin 0 → ℤ`. -/
abbrev emptyCoefficients : ModuleCat ℤ := ModuleCat.of ℤ (Fin 0 → ℤ)
/-- The integers as their canonical algebraic coefficient module. -/
abbrev integerCoefficients : ModuleCat ℤ := ModuleCat.of ℤ ℤ
/-- The integers as the supplied right module with their usual discrete topology. -/
abbrev integerModule : TopModuleCat ℤ := TopModuleCat.of ℤ ℤ
/-- The left-parenthesized tensor with singleton zero first coefficient module,
integer second coefficient module and supplied integer right factor. -/
noncomputable abbrev EmptyLeft := TopModuleCat.tensorLeftObj ℤ
  (ModuleCat.of ℤ (emptyCoefficients ⊗[ℤ] integerCoefficients)) integerModule
/-- The right-parenthesized tensor with singleton zero first coefficient module
and the inner one-sided tensor of the two integer factors. -/
noncomputable abbrev EmptyRight := TopModuleCat.tensorLeftObj ℤ emptyCoefficients
  (TopModuleCat.tensorLeftObj ℤ integerCoefficients integerModule)

/-- Reassociation at the singleton zero coefficient module `Fin 0 → ℤ`. -/
noncomputable def emptyAssoc : EmptyLeft ≃L[ℤ] EmptyRight :=
  TopModuleCat.tensorAssocContinuousLinearEquiv ℤ
    emptyCoefficients integerCoefficients integerModule

/-- The zero coefficient boundary collapses both parenthesizations and their
forward and inverse transports, with no nonzero assumption. -/
theorem emptyCoefficient_boundary :
    (∀ x : EmptyLeft, x = 0 ∧ emptyAssoc x = 0) ∧
      (∀ y : EmptyRight, y = 0 ∧ emptyAssoc.symm y = 0) := by
  have : Subsingleton EmptyLeft :=
    (inferInstance : Subsingleton (((Fin 0 → ℤ) ⊗[ℤ] ℤ) ⊗[ℤ] ℤ))
  have : Subsingleton EmptyRight :=
    (inferInstance : Subsingleton ((Fin 0 → ℤ) ⊗[ℤ] (ℤ ⊗[ℤ] ℤ)))
  constructor
  · intro x
    exact ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  · intro y
    exact ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩

end TensorAssociativityExamples

namespace TensorAssociativityExamples.CurriedLifts

/-- A scalar-valued continuous family obtained from two algebraic linear forms
and a continuous linear functional on the right factor. -/
noncomputable def coordinateFamily
    (p q : (ℤ × ℤ) →ₗ[ℤ] ℤ)
    (r : integerPairModule →L[ℤ] integerModule) :
    integerPairCoefficients →ₗ[ℤ]
      integerPairCoefficients →ₗ[ℤ] (integerPairModule →L[ℤ] integerModule) :=
  p.smulRight (q.smulRight r)

/-- The flat continuous lift of the scalar coordinate family. -/
noncomputable def flatCoordinateLift
    (p q : (ℤ × ℤ) →ₗ[ℤ] ℤ)
    (r : integerPairModule →L[ℤ] integerModule) : PairLeft →L[ℤ] integerModule :=
  TopModuleCat.tensorLiftCLM ℤ
    (C := ModuleCat.of ℤ (integerPairCoefficients ⊗[ℤ] integerPairCoefficients))
    (M := integerPairModule) (N := integerModule)
    (TensorProduct.lift (coordinateFamily p q r))

/-- The iterated continuous lift of the scalar coordinate family. -/
noncomputable def nestedCoordinateLift
    (p q : (ℤ × ℤ) →ₗ[ℤ] ℤ)
    (r : integerPairModule →L[ℤ] integerModule) : PairRight →L[ℤ] integerModule :=
  TopModuleCat.tensorLiftCLM ℤ (C := integerPairCoefficients)
    (M := TopModuleCat.tensorLeftObj ℤ integerPairCoefficients integerPairModule)
    (N := integerModule)
    ((TopModuleCat.tensorHomLinearEquiv ℤ integerPairCoefficients
      integerPairModule integerModule).symm.toLinearMap.comp (coordinateFamily p q r))

/-- Forgetting the two coordinate lifts recovers the algebraic detectors. -/
theorem coordinateLifts_toLinearMap
    (p q : (ℤ × ℤ) →ₗ[ℤ] ℤ)
    (r : integerPairModule →L[ℤ] integerModule) :
    (flatCoordinateLift p q r).toLinearMap = leftDetector p q r.toLinearMap ∧
      (nestedCoordinateLift p q r).toLinearMap = rightDetector p q r.toLinearMap := by
  have hfamily (c d : integerPairCoefficients) (m : integerPairModule) :
      coordinateFamily p q r c d m = p c * (q d * r m) := by
    calc
      _ = (p c • (q.smulRight r)) d m :=
        congrArg (fun k : integerPairCoefficients →ₗ[ℤ]
          (integerPairModule →L[ℤ] integerModule) ↦ k d m)
          (LinearMap.smulRight_apply p (q.smulRight r) c)
      _ = (p c • ((q.smulRight r) d)) m :=
        congrArg (fun k : integerPairModule →L[ℤ] integerModule ↦ k m)
          (LinearMap.smul_apply (p c) (q.smulRight r) d)
      _ = p c • ((q.smulRight r) d m) :=
        _root_.smul_apply ((q.smulRight r) d) (p c) m
      _ = p c • ((q d • r) m) :=
        congrArg (fun k : integerPairModule →L[ℤ] integerModule ↦ p c • k m)
          (LinearMap.smulRight_apply q r d)
      _ = p c • (q d • r m) :=
        congrArg (fun z : integerModule ↦ p c • z) (_root_.smul_apply r (q d) m)
      _ = p c * (q d * r m) := by rw [smul_eq_mul, smul_eq_mul]
  constructor
  · apply TensorProduct.ext_threefold
    intro c d m
    calc
      flatCoordinateLift p q r (show PairLeft from (c ⊗ₜ[ℤ] d) ⊗ₜ[ℤ] m) =
          coordinateFamily p q r c d m :=
        (TopModuleCat.tensorLiftCLM_tmul ℤ
          (C := ModuleCat.of ℤ (integerPairCoefficients ⊗[ℤ] integerPairCoefficients))
          (M := integerPairModule) (N := integerModule)
          (TensorProduct.lift (coordinateFamily p q r)) (c ⊗ₜ[ℤ] d) m).trans
            (congrArg (fun k : integerPairModule →L[ℤ] integerModule ↦ k m)
              (TensorProduct.lift.tmul (f' := coordinateFamily p q r) c d))
      _ = p c * (q d * r m) := hfamily c d m
      _ = (p c * q d) * r m := (mul_assoc (p c) (q d) (r m)).symm
      _ = leftDetector p q r.toLinearMap ((c ⊗ₜ[ℤ] d) ⊗ₜ[ℤ] m) :=
        (leftDetector_tmul p q r.toLinearMap c d m).symm
  · apply TensorProduct.ext_threefold'
    intro c d m
    calc
      nestedCoordinateLift p q r (show PairRight from c ⊗ₜ[ℤ] (d ⊗ₜ[ℤ] m)) =
          ((TopModuleCat.tensorHomLinearEquiv ℤ integerPairCoefficients
            integerPairModule integerModule).symm.toLinearMap.comp
              (coordinateFamily p q r)) c
                (show TopModuleCat.tensorLeftObj ℤ integerPairCoefficients
                  integerPairModule from d ⊗ₜ[ℤ] m) :=
        TopModuleCat.tensorLiftCLM_tmul ℤ (C := integerPairCoefficients)
          (M := TopModuleCat.tensorLeftObj ℤ integerPairCoefficients integerPairModule)
          (N := integerModule)
          ((TopModuleCat.tensorHomLinearEquiv ℤ integerPairCoefficients
            integerPairModule integerModule).symm.toLinearMap.comp (coordinateFamily p q r))
          c (show TopModuleCat.tensorLeftObj ℤ integerPairCoefficients
            integerPairModule from d ⊗ₜ[ℤ] m)
      _ = (TopModuleCat.tensorHomLinearEquiv ℤ integerPairCoefficients
          integerPairModule integerModule).symm (coordinateFamily p q r c)
            (show TopModuleCat.tensorLeftObj ℤ integerPairCoefficients
              integerPairModule from d ⊗ₜ[ℤ] m) :=
        congrArg (fun k : TopModuleCat.tensorLeftObj ℤ integerPairCoefficients
          integerPairModule →L[ℤ] integerModule ↦
            k (show TopModuleCat.tensorLeftObj ℤ integerPairCoefficients
              integerPairModule from d ⊗ₜ[ℤ] m))
          ((LinearMap.comp_apply
            (TopModuleCat.tensorHomLinearEquiv ℤ integerPairCoefficients
              integerPairModule integerModule).symm.toLinearMap (coordinateFamily p q r) c).trans
                (congrFun (LinearEquiv.coe_toLinearMap
                  (TopModuleCat.tensorHomLinearEquiv ℤ integerPairCoefficients
                    integerPairModule integerModule).symm) (coordinateFamily p q r c)))
      _ = coordinateFamily p q r c d m :=
        TopModuleCat.tensorHomLinearEquiv_symm_apply_tmul ℤ
          (C := integerPairCoefficients) (M := integerPairModule) (N := integerModule)
          (coordinateFamily p q r c) d m
      _ = p c * (q d * r m) := hfamily c d m
      _ = rightDetector p q r.toLinearMap (c ⊗ₜ[ℤ] (d ⊗ₜ[ℤ] m)) :=
        (rightDetector_tmul p q r.toLinearMap c d m).symm

/-- Whole lift and curry compatibility preserves algebraic detector values on
all flat and nested tensors, not only pure triples. -/
theorem coordinateLifts_detected
    (p q : (ℤ × ℤ) →ₗ[ℤ] ℤ)
    (r : integerPairModule →L[ℤ] integerModule) (z : PairLeft) (w : PairRight) :
    flatCoordinateLift p q r =
        (nestedCoordinateLift p q r).comp integerPairAssoc.toContinuousLinearMap ∧
      TopModuleCat.tensorCurry ℤ
          ((nestedCoordinateLift p q r).comp integerPairAssoc.toContinuousLinearMap) =
        TensorProduct.lift
          ((TopModuleCat.tensorHomLinearEquiv ℤ integerPairCoefficients
            integerPairModule integerModule).toLinearMap.comp
              (TopModuleCat.tensorCurry ℤ (nestedCoordinateLift p q r))) ∧
      flatCoordinateLift p q r z =
        rightDetector p q r.toLinearMap (integerPairAssoc z) ∧
      nestedCoordinateLift p q r w =
        leftDetector p q r.toLinearMap (integerPairAssoc.symm w) := by
  have hlift : flatCoordinateLift p q r =
      (nestedCoordinateLift p q r).comp integerPairAssoc.toContinuousLinearMap :=
    TopModuleCat.tensorLiftCLM_lift_eq_comp_tensorAssoc ℤ
      integerPairCoefficients integerPairCoefficients integerPairModule integerModule
      (coordinateFamily p q r)
  refine ⟨hlift, ?_, ?_, ?_⟩
  · exact TopModuleCat.tensorCurry_comp_tensorAssoc ℤ
      integerPairCoefficients integerPairCoefficients integerPairModule integerModule
      (nestedCoordinateLift p q r)
  · calc
      flatCoordinateLift p q r z = nestedCoordinateLift p q r (integerPairAssoc z) :=
        DFunLike.congr_fun hlift z
      _ = rightDetector p q r.toLinearMap (integerPairAssoc z) :=
        DFunLike.congr_fun (coordinateLifts_toLinearMap p q r).2 (integerPairAssoc z)
  · calc
      nestedCoordinateLift p q r w = flatCoordinateLift p q r (integerPairAssoc.symm w) := by
        simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
          ContinuousLinearEquiv.apply_symm_apply] using
            (DFunLike.congr_fun hlift (integerPairAssoc.symm w)).symm
      _ = leftDetector p q r.toLinearMap (integerPairAssoc.symm w) :=
        DFunLike.congr_fun (coordinateLifts_toLinearMap p q r).1 (integerPairAssoc.symm w)

/-- Mixed tensors retain both varying right coordinates, and the weighted
coordinate functional reads three on the mixed unit specimen. -/
theorem coordinateLifts_mixed_variables (s t : ℤ) :
    flatCoordinateLift p1 p2 (ContinuousLinearMap.fst ℤ ℤ ℤ)
        (mixedLeft (s, t)) = s ∧
      nestedCoordinateLift p1 p2 (ContinuousLinearMap.fst ℤ ℤ ℤ)
        (mixedRight (s, t)) = s ∧
      flatCoordinateLift p2 p1 (ContinuousLinearMap.snd ℤ ℤ ℤ)
        (mixedLeft (s, t)) = t ∧
      nestedCoordinateLift p2 p1 (ContinuousLinearMap.snd ℤ ℤ ℤ)
        (mixedRight (s, t)) = t ∧
      TopModuleCat.tensorCurry ℤ
        ((nestedCoordinateLift p1 p2 (ContinuousLinearMap.fst ℤ ℤ ℤ)).comp
          integerPairAssoc.toContinuousLinearMap) mixedCoefficient (s, t) = s ∧
      (nestedCoordinateLift p1 p2 (ContinuousLinearMap.fst ℤ ℤ ℤ) +
        (2 : ℤ) • nestedCoordinateLift p2 p1 (ContinuousLinearMap.fst ℤ ℤ ℤ))
          (mixedRight e1) = 3 := by
  have hflat12 :
      (flatCoordinateLift p1 p2 (ContinuousLinearMap.fst ℤ ℤ ℤ)).toLinearMap =
        leftDetection12 :=
    (coordinateLifts_toLinearMap p1 p2 (ContinuousLinearMap.fst ℤ ℤ ℤ)).1
  have hnested12 :
      (nestedCoordinateLift p1 p2 (ContinuousLinearMap.fst ℤ ℤ ℤ)).toLinearMap =
        rightDetection12 :=
    (coordinateLifts_toLinearMap p1 p2 (ContinuousLinearMap.fst ℤ ℤ ℤ)).2
  have hflat212 :
      (flatCoordinateLift p2 p1 (ContinuousLinearMap.snd ℤ ℤ ℤ)).toLinearMap =
        leftDetector p2 p1 p2 :=
    (coordinateLifts_toLinearMap p2 p1 (ContinuousLinearMap.snd ℤ ℤ ℤ)).1
  have hnested212 :
      (nestedCoordinateLift p2 p1 (ContinuousLinearMap.snd ℤ ℤ ℤ)).toLinearMap =
        rightDetector p2 p1 p2 :=
    (coordinateLifts_toLinearMap p2 p1 (ContinuousLinearMap.snd ℤ ℤ ℤ)).2
  refine ⟨(DFunLike.congr_fun hflat12 _).trans
      (integerPair_variable_coordinates s t).2.1,
    (DFunLike.congr_fun hnested12 _).trans
      (integerPair_variable_coordinates s t).2.2.1,
    (DFunLike.congr_fun hflat212 _).trans
      (integerPair_variable_coordinates s t).2.2.2.1,
    (DFunLike.congr_fun hnested212 _).trans
      (integerPair_variable_coordinates s t).2.2.2.2, ?_, ?_⟩
  · rw [TopModuleCat.tensorCurry_apply_apply]
    change nestedCoordinateLift p1 p2 (ContinuousLinearMap.fst ℤ ℤ ℤ)
      (integerPairAssoc (mixedLeft (s, t))) = s
    rw [(integerPair_variable_coordinates s t).1]
    exact (DFunLike.congr_fun hnested12 _).trans
      (integerPair_variable_coordinates s t).2.2.1
  · have hnested21 :
        (nestedCoordinateLift p2 p1 (ContinuousLinearMap.fst ℤ ℤ ℤ)).toLinearMap =
          rightDetection21 :=
      (coordinateLifts_toLinearMap p2 p1 (ContinuousLinearMap.fst ℤ ℤ ℤ)).2
    change nestedCoordinateLift p1 p2 (ContinuousLinearMap.fst ℤ ℤ ℤ) (mixedRight e1) +
      (2 : ℤ) • nestedCoordinateLift p2 p1 (ContinuousLinearMap.fst ℤ ℤ ℤ)
        (mixedRight e1) = 3
    exact (congrArg₂ (fun a b : ℤ ↦ a + (2 : ℤ) • b)
      (DFunLike.congr_fun hnested12 (mixedRight e1))
      (DFunLike.congr_fun hnested21 (mixedRight e1))).trans
        integerPair_mixed.2.2.2.2.2.2

/-- Two different nonzero coefficient functionals and their outgoing lifts are
distinguished by the supplied pure triple; mixed lifts are also nonzero. -/
theorem coordinateLifts_nonzero_distinct :
    coordinateFamily p1 p2 (ContinuousLinearMap.fst ℤ ℤ ℤ) e1 e2 e1 = 1 ∧
      coordinateFamily p2 p1 (ContinuousLinearMap.fst ℤ ℤ ℤ) e1 e2 e1 = 0 ∧
      flatCoordinateLift p1 p2 (ContinuousLinearMap.fst ℤ ℤ ℤ) leftTriple = 1 ∧
      nestedCoordinateLift p1 p2 (ContinuousLinearMap.fst ℤ ℤ ℤ) rightTriple = 1 ∧
      coordinateFamily p1 p2 (ContinuousLinearMap.fst ℤ ℤ ℤ) ≠
        coordinateFamily p2 p1 (ContinuousLinearMap.fst ℤ ℤ ℤ) ∧
      nestedCoordinateLift p1 p2 (ContinuousLinearMap.fst ℤ ℤ ℤ) ≠
        nestedCoordinateLift p2 p1 (ContinuousLinearMap.fst ℤ ℤ ℤ) ∧
      flatCoordinateLift p1 p2 (ContinuousLinearMap.fst ℤ ℤ ℤ) (mixedLeft e1) ≠ 0 ∧
      nestedCoordinateLift p1 p2 (ContinuousLinearMap.fst ℤ ℤ ℤ) (mixedRight e1) ≠ 0 := by
  have hfamily12 :
      coordinateFamily p1 p2 (ContinuousLinearMap.fst ℤ ℤ ℤ) e1 e2 e1 = 1 := by
    simp [coordinateFamily, LinearMap.smulRight_apply, p1, p2, e1, e2]
  have hfamily21 :
      coordinateFamily p2 p1 (ContinuousLinearMap.fst ℤ ℤ ℤ) e1 e2 e1 = 0 := by
    simp [coordinateFamily, LinearMap.smulRight_apply, p1, p2, e1, e2]
  have hflat : flatCoordinateLift p1 p2 (ContinuousLinearMap.fst ℤ ℤ ℤ) leftTriple = 1 :=
    (DFunLike.congr_fun
      (coordinateLifts_toLinearMap p1 p2 (ContinuousLinearMap.fst ℤ ℤ ℤ)).1
      leftTriple).trans integerPair_nonzero.1
  have hnested :
      nestedCoordinateLift p1 p2 (ContinuousLinearMap.fst ℤ ℤ ℤ) rightTriple = 1 :=
    (DFunLike.congr_fun
      (coordinateLifts_toLinearMap p1 p2 (ContinuousLinearMap.fst ℤ ℤ ℤ)).2
      rightTriple).trans integerPair_nonzero.2.1
  have hnested21 :
      nestedCoordinateLift p2 p1 (ContinuousLinearMap.fst ℤ ℤ ℤ) rightTriple = 0 := by
    calc
      _ = rightDetector p2 p1 p1 rightTriple :=
        DFunLike.congr_fun
          (coordinateLifts_toLinearMap p2 p1 (ContinuousLinearMap.fst ℤ ℤ ℤ)).2 rightTriple
      _ = 0 := (rightDetector_tmul p2 p1 p1 e1 e2 e1).trans
        (by simp [p1, p2, e1, e2])
  have hflatMixed :
      flatCoordinateLift p1 p2 (ContinuousLinearMap.fst ℤ ℤ ℤ) (mixedLeft e1) = 1 :=
    (DFunLike.congr_fun
      (coordinateLifts_toLinearMap p1 p2 (ContinuousLinearMap.fst ℤ ℤ ℤ)).1
      (mixedLeft e1)).trans integerPair_mixed.2.2.1
  have hnestedMixed :
      nestedCoordinateLift p1 p2 (ContinuousLinearMap.fst ℤ ℤ ℤ) (mixedRight e1) = 1 :=
    (DFunLike.congr_fun
      (coordinateLifts_toLinearMap p1 p2 (ContinuousLinearMap.fst ℤ ℤ ℤ)).2
      (mixedRight e1)).trans integerPair_mixed.2.2.2.2.1
  refine ⟨hfamily12, hfamily21, hflat, hnested, ?_, ?_, ?_, ?_⟩
  · intro h
    have hvalue := congrArg
      (fun b : integerPairCoefficients →ₗ[ℤ]
        integerPairCoefficients →ₗ[ℤ] (integerPairModule →L[ℤ] integerModule) ↦
          b e1 e2 e1) h
    exact one_ne_zero (hfamily12.symm.trans (hvalue.trans hfamily21))
  · intro h
    have hvalue := congrArg (fun f : PairRight →L[ℤ] integerModule ↦ f rightTriple) h
    exact one_ne_zero (hnested.symm.trans (hvalue.trans hnested21))
  · intro h
    exact one_ne_zero (hflatMixed.symm.trans h)
  · intro h
    exact one_ne_zero (hnestedMixed.symm.trans h)

open ProjectiveTensorSeparationExamples

/-- The flat tensor with infinite integer coefficients, regular inner coefficients
and the usual real right factor. -/
noncomputable abbrev InfiniteFlat := TopModuleCat.tensorLeftObj ℤ
  (ModuleCat.of ℤ (infiniteCoefficients ⊗[ℤ] ModuleCat.of ℤ ℤ)) realModule

/-- The corresponding nested tensor with the usual real right factor. -/
noncomputable abbrev InfiniteNested := TopModuleCat.tensorLeftObj ℤ infiniteCoefficients
  (TopModuleCat.tensorLeftObj ℤ (ModuleCat.of ℤ ℤ) realModule)

/-- The first infinite coefficient coordinate, followed by two scalar actions on reals. -/
noncomputable def infiniteRealFamily : infiniteCoefficients →ₗ[ℤ]
    ModuleCat.of ℤ ℤ →ₗ[ℤ] (realModule →L[ℤ] realModule) :=
  (infiniteBasis.coord 0).smulRight
    ((LinearMap.id : ℤ →ₗ[ℤ] ℤ).smulRight (ContinuousLinearMap.id ℤ realModule))

/-- The flat lift of the first-coordinate real family. -/
noncomputable def infiniteRealFlatLift : InfiniteFlat →L[ℤ] realModule :=
  TopModuleCat.tensorLiftCLM ℤ
    (C := ModuleCat.of ℤ (infiniteCoefficients ⊗[ℤ] ModuleCat.of ℤ ℤ))
    (M := realModule) (N := realModule) (TensorProduct.lift infiniteRealFamily)

/-- The iterated lift of the first-coordinate real family. -/
noncomputable def infiniteRealNestedLift : InfiniteNested →L[ℤ] realModule :=
  TopModuleCat.tensorLiftCLM ℤ (C := infiniteCoefficients)
    (M := TopModuleCat.tensorLeftObj ℤ (ModuleCat.of ℤ ℤ) realModule) (N := realModule)
    ((TopModuleCat.tensorHomLinearEquiv ℤ (ModuleCat.of ℤ ℤ)
      realModule realModule).symm.toLinearMap.comp infiniteRealFamily)

/-- Lift and curry compatibility acts nontrivially with nonfinite coefficients
and a nondiscrete supplied right factor. -/
theorem infiniteReal_lift_curry_controls (x : InfiniteFlat) (y : InfiniteNested) :
    ¬ Module.Finite ℤ infiniteCoefficients ∧ ¬ DiscreteTopology realModule ∧
      (infiniteRealFlatLift x = infiniteRealNestedLift
        (TopModuleCat.tensorAssocContinuousLinearEquiv ℤ infiniteCoefficients
          (ModuleCat.of ℤ ℤ) realModule x) ∧
       infiniteRealNestedLift y = infiniteRealFlatLift
        ((TopModuleCat.tensorAssocContinuousLinearEquiv ℤ infiniteCoefficients
          (ModuleCat.of ℤ ℤ) realModule).symm y) ∧
       TopModuleCat.tensorCurry ℤ
          (infiniteRealNestedLift.comp
            (TopModuleCat.tensorAssocContinuousLinearEquiv ℤ infiniteCoefficients
              (ModuleCat.of ℤ ℤ) realModule).toContinuousLinearMap) =
         TensorProduct.lift
          ((TopModuleCat.tensorHomLinearEquiv ℤ (ModuleCat.of ℤ ℤ)
            realModule realModule).toLinearMap.comp
              (TopModuleCat.tensorCurry ℤ infiniteRealNestedLift)) ∧
       infiniteRealFamily (integerBasisVector 0) 1 1 = 1 ∧
       infiniteRealFlatLift ((integerBasisVector 0 ⊗ₜ[ℤ] (1 : ℤ)) ⊗ₜ[ℤ]
         (1 : realModule)) = 1 ∧
       infiniteRealNestedLift (integerBasisVector 0 ⊗ₜ[ℤ]
         ((1 : ℤ) ⊗ₜ[ℤ] (1 : realModule))) = 1) :=
  ⟨infiniteCoefficients_not_finite, realModule_not_discrete, by
    let α : InfiniteFlat ≃L[ℤ] InfiniteNested :=
      TopModuleCat.tensorAssocContinuousLinearEquiv ℤ infiniteCoefficients
        (ModuleCat.of ℤ ℤ) realModule
    have hlift : infiniteRealFlatLift = infiniteRealNestedLift.comp α.toContinuousLinearMap :=
      TopModuleCat.tensorLiftCLM_lift_eq_comp_tensorAssoc ℤ infiniteCoefficients
        (ModuleCat.of ℤ ℤ) realModule realModule infiniteRealFamily
    have hb : integerBasisVector 0 = infiniteBasis 0 := by
      simp [integerBasisVector, infiniteBasis]
    have hcoord : infiniteBasis.coord 0 (integerBasisVector 0) = 1 := by
      simp [hb, Module.Basis.coord_apply]
    have hfamily : infiniteRealFamily (integerBasisVector 0) 1 1 = 1 := by
      simp only [infiniteRealFamily, LinearMap.smulRight_apply,
        LinearMap.id_apply, ContinuousLinearMap.id_apply, hcoord, one_smul]
    refine ⟨?_, ?_, ?_, hfamily, ?_, ?_⟩
    · calc
        infiniteRealFlatLift x =
            (infiniteRealNestedLift.comp α.toContinuousLinearMap) x :=
          DFunLike.congr_fun hlift x
        _ = infiniteRealNestedLift (α.toContinuousLinearMap x) :=
          ContinuousLinearMap.comp_apply infiniteRealNestedLift α.toContinuousLinearMap x
        _ = infiniteRealNestedLift (α x) :=
          congrArg infiniteRealNestedLift (ContinuousLinearEquiv.coe_apply α x)
    · calc
        infiniteRealNestedLift y = infiniteRealNestedLift (α (α.symm y)) :=
          congrArg infiniteRealNestedLift (α.apply_symm_apply y).symm
        _ = (infiniteRealNestedLift.comp α.toContinuousLinearMap) (α.symm y) :=
          ((ContinuousLinearMap.comp_apply infiniteRealNestedLift
            α.toContinuousLinearMap (α.symm y)).trans
              (congrArg infiniteRealNestedLift
                (ContinuousLinearEquiv.coe_apply α (α.symm y)))).symm
        _ = infiniteRealFlatLift (α.symm y) :=
          (DFunLike.congr_fun hlift (α.symm y)).symm
    · exact TopModuleCat.tensorCurry_comp_tensorAssoc ℤ infiniteCoefficients
        (ModuleCat.of ℤ ℤ) realModule realModule infiniteRealNestedLift
    · calc
        infiniteRealFlatLift
            (show InfiniteFlat from (integerBasisVector 0 ⊗ₜ[ℤ] (1 : ℤ)) ⊗ₜ[ℤ]
              (1 : realModule)) = infiniteRealFamily (integerBasisVector 0) 1 1 :=
          (TopModuleCat.tensorLiftCLM_tmul ℤ
            (C := ModuleCat.of ℤ (infiniteCoefficients ⊗[ℤ] ModuleCat.of ℤ ℤ))
            (M := realModule) (N := realModule) (TensorProduct.lift infiniteRealFamily)
            (integerBasisVector 0 ⊗ₜ[ℤ] (1 : ℤ)) (1 : realModule)).trans
              (congrArg (fun k : realModule →L[ℤ] realModule ↦ k (1 : realModule))
                (TensorProduct.lift.tmul (f' := infiniteRealFamily)
                  (integerBasisVector 0) (1 : ℤ)))
        _ = 1 := hfamily
    · calc
        infiniteRealNestedLift
            (show InfiniteNested from integerBasisVector 0 ⊗ₜ[ℤ]
              ((1 : ℤ) ⊗ₜ[ℤ] (1 : realModule))) =
            ((TopModuleCat.tensorHomLinearEquiv ℤ (ModuleCat.of ℤ ℤ)
              realModule realModule).symm.toLinearMap.comp infiniteRealFamily)
                (integerBasisVector 0)
                (show TopModuleCat.tensorLeftObj ℤ (ModuleCat.of ℤ ℤ) realModule from
                  (1 : ℤ) ⊗ₜ[ℤ] (1 : realModule)) :=
          TopModuleCat.tensorLiftCLM_tmul ℤ (C := infiniteCoefficients)
            (M := TopModuleCat.tensorLeftObj ℤ (ModuleCat.of ℤ ℤ) realModule) (N := realModule)
            ((TopModuleCat.tensorHomLinearEquiv ℤ (ModuleCat.of ℤ ℤ)
              realModule realModule).symm.toLinearMap.comp infiniteRealFamily)
            (integerBasisVector 0)
            (show TopModuleCat.tensorLeftObj ℤ (ModuleCat.of ℤ ℤ) realModule from
              (1 : ℤ) ⊗ₜ[ℤ] (1 : realModule))
        _ = (TopModuleCat.tensorHomLinearEquiv ℤ (ModuleCat.of ℤ ℤ)
            realModule realModule).symm (infiniteRealFamily (integerBasisVector 0))
              (show TopModuleCat.tensorLeftObj ℤ (ModuleCat.of ℤ ℤ) realModule from
                (1 : ℤ) ⊗ₜ[ℤ] (1 : realModule)) :=
          congrArg (fun k : TopModuleCat.tensorLeftObj ℤ (ModuleCat.of ℤ ℤ)
            realModule →L[ℤ] realModule ↦
              k (show TopModuleCat.tensorLeftObj ℤ (ModuleCat.of ℤ ℤ) realModule from
                (1 : ℤ) ⊗ₜ[ℤ] (1 : realModule)))
            ((LinearMap.comp_apply
              (TopModuleCat.tensorHomLinearEquiv ℤ (ModuleCat.of ℤ ℤ)
                realModule realModule).symm.toLinearMap infiniteRealFamily
                  (integerBasisVector 0)).trans
                    (congrFun (LinearEquiv.coe_toLinearMap
                      (TopModuleCat.tensorHomLinearEquiv ℤ (ModuleCat.of ℤ ℤ)
                        realModule realModule).symm) (infiniteRealFamily (integerBasisVector 0))))
        _ = infiniteRealFamily (integerBasisVector 0) 1 1 :=
          TopModuleCat.tensorHomLinearEquiv_symm_apply_tmul ℤ
            (C := ModuleCat.of ℤ ℤ) (M := realModule) (N := realModule)
            (infiniteRealFamily (integerBasisVector 0)) (1 : ℤ) (1 : realModule)
        _ = 1 := hfamily⟩

/-- The flat tensor with the first-axis ideal and regular inner/right factors. -/
noncomputable abbrev IdealFlat := TopModuleCat.tensorLeftObj productRing
  (ModuleCat.of productRing
    (firstAxisCoefficients ⊗[productRing] ModuleCat.of productRing productRing)) productModule

/-- The corresponding nested tensor with regular inner/right factors. -/
noncomputable abbrev IdealNested := TopModuleCat.tensorLeftObj productRing firstAxisCoefficients
  (TopModuleCat.tensorLeftObj productRing (ModuleCat.of productRing productRing) productModule)

/-- The ideal inclusion, followed by two regular scalar actions. -/
noncomputable def idealFamily : firstAxisCoefficients →ₗ[productRing]
    ModuleCat.of productRing productRing →ₗ[productRing]
      (productModule →L[productRing] productModule) :=
  firstAxisIdeal.subtype.smulRight
    ((LinearMap.id : productRing →ₗ[productRing] productRing).smulRight
      (ContinuousLinearMap.id productRing productModule))

/-- The flat lift of the ideal-inclusion family. -/
noncomputable def idealFlatLift : IdealFlat →L[productRing] productModule :=
  TopModuleCat.tensorLiftCLM productRing
    (C := ModuleCat.of productRing
      (firstAxisCoefficients ⊗[productRing] ModuleCat.of productRing productRing))
    (M := productModule) (N := productModule) (TensorProduct.lift idealFamily)

/-- The iterated lift of the ideal-inclusion family. -/
noncomputable def idealNestedLift : IdealNested →L[productRing] productModule :=
  TopModuleCat.tensorLiftCLM productRing (C := firstAxisCoefficients)
    (M := TopModuleCat.tensorLeftObj productRing
      (ModuleCat.of productRing productRing) productModule)
    (N := productModule)
    ((TopModuleCat.tensorHomLinearEquiv productRing (ModuleCat.of productRing productRing)
      productModule productModule).symm.toLinearMap.comp idealFamily)

/-- The compatibility laws give nonzero idempotent values with nonfree coefficients,
while retaining the ideal detector `firstAxisTensorValue` as a separate continuous map. -/
theorem ideal_lift_curry_controls (x : IdealFlat) (y : IdealNested) :
    ¬ Module.Free productRing firstAxisCoefficients ∧ firstAxisElement ≠ 0 ∧
      firstAxisTensorValue firstAxisTensor = firstAxisIdempotent ∧
      (idealFlatLift x = idealNestedLift
        (TopModuleCat.tensorAssocContinuousLinearEquiv productRing firstAxisCoefficients
          (ModuleCat.of productRing productRing) productModule x) ∧
       idealNestedLift y = idealFlatLift
        ((TopModuleCat.tensorAssocContinuousLinearEquiv productRing firstAxisCoefficients
          (ModuleCat.of productRing productRing) productModule).symm y) ∧
       TopModuleCat.tensorCurry productRing
          (idealNestedLift.comp
            (TopModuleCat.tensorAssocContinuousLinearEquiv productRing firstAxisCoefficients
              (ModuleCat.of productRing productRing) productModule).toContinuousLinearMap) =
         TensorProduct.lift
          ((TopModuleCat.tensorHomLinearEquiv productRing (ModuleCat.of productRing productRing)
            productModule productModule).toLinearMap.comp
              (TopModuleCat.tensorCurry productRing idealNestedLift)) ∧
       idealFamily firstAxisElement 1 1 = firstAxisIdempotent ∧
       idealFlatLift ((firstAxisElement ⊗ₜ[productRing] (1 : productRing)) ⊗ₜ[productRing]
         (1 : productModule)) = firstAxisIdempotent ∧
       idealNestedLift (firstAxisElement ⊗ₜ[productRing]
         ((1 : productRing) ⊗ₜ[productRing] (1 : productModule))) = firstAxisIdempotent) :=
  ⟨firstAxisCoefficients_not_free, firstAxisElement_ne_zero, firstAxisTensorValue_first,
    by
      let α : IdealFlat ≃L[productRing] IdealNested :=
        TopModuleCat.tensorAssocContinuousLinearEquiv productRing firstAxisCoefficients
          (ModuleCat.of productRing productRing) productModule
      have hlift : idealFlatLift = idealNestedLift.comp α.toContinuousLinearMap :=
        TopModuleCat.tensorLiftCLM_lift_eq_comp_tensorAssoc productRing firstAxisCoefficients
          (ModuleCat.of productRing productRing) productModule productModule idealFamily
      have hfamily : idealFamily firstAxisElement 1 1 = firstAxisIdempotent := by
        simp [idealFamily, LinearMap.smulRight_apply, firstAxisElement, smul_eq_mul]
      refine ⟨?_, ?_, ?_, hfamily, ?_, ?_⟩
      · calc
          idealFlatLift x = (idealNestedLift.comp α.toContinuousLinearMap) x :=
            DFunLike.congr_fun hlift x
          _ = idealNestedLift (α.toContinuousLinearMap x) :=
            ContinuousLinearMap.comp_apply idealNestedLift α.toContinuousLinearMap x
          _ = idealNestedLift (α x) :=
            congrArg idealNestedLift (ContinuousLinearEquiv.coe_apply α x)
      · calc
          idealNestedLift y = idealNestedLift (α (α.symm y)) :=
            congrArg idealNestedLift (α.apply_symm_apply y).symm
          _ = (idealNestedLift.comp α.toContinuousLinearMap) (α.symm y) :=
            ((ContinuousLinearMap.comp_apply idealNestedLift
              α.toContinuousLinearMap (α.symm y)).trans
                (congrArg idealNestedLift
                  (ContinuousLinearEquiv.coe_apply α (α.symm y)))).symm
          _ = idealFlatLift (α.symm y) := (DFunLike.congr_fun hlift (α.symm y)).symm
      · exact TopModuleCat.tensorCurry_comp_tensorAssoc productRing firstAxisCoefficients
          (ModuleCat.of productRing productRing) productModule productModule idealNestedLift
      · calc
          idealFlatLift
              (show IdealFlat from (firstAxisElement ⊗ₜ[productRing] (1 : productRing))
                ⊗ₜ[productRing] (1 : productModule)) =
              idealFamily firstAxisElement 1 1 :=
            (TopModuleCat.tensorLiftCLM_tmul productRing
              (C := ModuleCat.of productRing
                (firstAxisCoefficients ⊗[productRing] ModuleCat.of productRing productRing))
              (M := productModule) (N := productModule) (TensorProduct.lift idealFamily)
              (firstAxisElement ⊗ₜ[productRing] (1 : productRing)) (1 : productModule)).trans
                (congrArg (fun k : productModule →L[productRing] productModule ↦
                  k (1 : productModule))
                  (TensorProduct.lift.tmul (f' := idealFamily)
                    firstAxisElement (1 : productRing)))
          _ = firstAxisIdempotent := hfamily
      · calc
          idealNestedLift
              (show IdealNested from firstAxisElement ⊗ₜ[productRing]
                ((1 : productRing) ⊗ₜ[productRing] (1 : productModule))) =
              ((TopModuleCat.tensorHomLinearEquiv productRing (ModuleCat.of productRing productRing)
                productModule productModule).symm.toLinearMap.comp idealFamily) firstAxisElement
                  (show TopModuleCat.tensorLeftObj productRing
                    (ModuleCat.of productRing productRing) productModule from
                      (1 : productRing) ⊗ₜ[productRing] (1 : productModule)) :=
            TopModuleCat.tensorLiftCLM_tmul productRing (C := firstAxisCoefficients)
              (M := TopModuleCat.tensorLeftObj productRing
                (ModuleCat.of productRing productRing) productModule) (N := productModule)
              ((TopModuleCat.tensorHomLinearEquiv productRing (ModuleCat.of productRing productRing)
                productModule productModule).symm.toLinearMap.comp idealFamily) firstAxisElement
              (show TopModuleCat.tensorLeftObj productRing
                (ModuleCat.of productRing productRing) productModule from
                  (1 : productRing) ⊗ₜ[productRing] (1 : productModule))
          _ = (TopModuleCat.tensorHomLinearEquiv productRing (ModuleCat.of productRing productRing)
              productModule productModule).symm (idealFamily firstAxisElement)
                (show TopModuleCat.tensorLeftObj productRing
                  (ModuleCat.of productRing productRing) productModule from
                    (1 : productRing) ⊗ₜ[productRing] (1 : productModule)) :=
            congrArg (fun k : TopModuleCat.tensorLeftObj productRing
              (ModuleCat.of productRing productRing) productModule →L[productRing] productModule ↦
                k (show TopModuleCat.tensorLeftObj productRing
                  (ModuleCat.of productRing productRing) productModule from
                    (1 : productRing) ⊗ₜ[productRing] (1 : productModule)))
              ((LinearMap.comp_apply
                (TopModuleCat.tensorHomLinearEquiv productRing
                  (ModuleCat.of productRing productRing) productModule
                    productModule).symm.toLinearMap
                    idealFamily firstAxisElement).trans
                    (congrFun (LinearEquiv.coe_toLinearMap
                      (TopModuleCat.tensorHomLinearEquiv productRing
                        (ModuleCat.of productRing productRing) productModule productModule).symm)
                          (idealFamily firstAxisElement)))
          _ = idealFamily firstAxisElement 1 1 :=
            TopModuleCat.tensorHomLinearEquiv_symm_apply_tmul productRing
              (C := ModuleCat.of productRing productRing) (M := productModule) (N := productModule)
              (idealFamily firstAxisElement) (1 : productRing) (1 : productModule)
          _ = firstAxisIdempotent := hfamily⟩

end TensorAssociativityExamples.CurriedLifts
