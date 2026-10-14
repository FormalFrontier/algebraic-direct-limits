/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicDirectLimits.Topology.TensorProduct
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

/-!
# Binary products of one-sided topological tensors

`TopModuleCat.tensorProdRight` realizes Mathlib's algebraic `TensorProduct.prodRight`
as a continuous linear equivalence. Its source tensors an algebraic coefficient
module with the product of two topological modules. Its target is the ordinary
product of the two one-sided tensor objects, with the product topology and action.
The coefficient module has no topology, and all carrier universes are independent.

The characteristic API for `tensorProdRight` describes the underlying equivalence,
generators, arbitrary inverse reconstruction, projections, inclusions, uniqueness
and naturality. The forward continuous linear map is the product of the tensor
projections; the inverse is the coproduct of the tensor inclusions. Generic
equivalence round trips and extensionality for maps out of the tensor are supplied
by the existing APIs.

`TopModuleCat.tensorProdLeft` has Mathlib's `TensorProduct.prodLeft` as its
underlying linear equivalence, distributing an algebraic binary product of
coefficients against a topological right module. Neither coefficient module
carries a topology; the right module and the scalar ring retain their supplied
topologies, with jointly continuous right scalar action and independent carriers.
The module categories use additive groups and a commutative ring. Mathlib's
algebraic equivalence also admits commutative semirings and an auxiliary scalar
ring acting on both coefficient modules, with compatible scalar towers; that
additional scalar action is not required on the right factor.

## Implementation notes

The forward map of `tensorProdLeft` is the product of the coefficient tensor
projections, and its inverse is the coproduct of the coefficient tensor
inclusions. Their agreement with the algebraic equivalence gives continuity
in both directions and the characteristic and naturality formulas.

## References

Mathlib's algebraic tensor-product distribution over binary products is due to
Eric Wieser. Its tensor-map, unitor and scalar-tower APIs are due to Kenny Lau
and Mario Carneiro. The one-sided topology, generators and linear continuity
criterion follow Formal Frontier Agents' topological tensor development and the
Continuous Group Cohomology formalization, including Beacon's original
topological development. Mathlib's topological-module category and coinduced
construction are due to Richard Hill and Andrew Yang. The continuous-linear-map
and equivalence APIs are due to Jan-David Salchow, Sébastien Gouëzel, Jean Lo,
Yury Kudryashov, Frédéric Dupuis and Heather Macbeth. This module is an original
Formal Frontier contribution developed with AI assistance.
-/

@[expose] public section

open scoped TensorProduct

universe uR uC uM uN uD uM' uN'

namespace TopModuleCat

variable (R : Type uR) [CommRing R] [TopologicalSpace R]
variable (C : ModuleCat.{uC} R) (M : TopModuleCat.{uM} R) (N : TopModuleCat.{uN} R)

/-- The tensor projections realize Mathlib's algebraic forward map. Agreement is
checked on pure tensors using `TensorProduct.prodRight_tmul`. -/
private theorem prodRight_toLinearMap_eq :
    (show tensorLeftObj R C (TopModuleCat.of R (M × N)) →ₗ[R]
      (tensorLeftObj R C M × tensorLeftObj R C N) from
        (TensorProduct.prodRight R R C M N).toLinearMap) =
      ((tensorMapCLM R (C := C) (D := C)
        (M := TopModuleCat.of R (M × N)) (N := M)
        (LinearMap.id : C →ₗ[R] C) (ContinuousLinearMap.fst R M N)).prod
      (tensorMapCLM R (C := C) (D := C)
        (M := TopModuleCat.of R (M × N)) (N := N)
        (LinearMap.id : C →ₗ[R] C) (ContinuousLinearMap.snd R M N))).toLinearMap := by
  apply TensorProduct.ext'
  intro c p
  exact TensorProduct.prodRight_tmul R R C M N c p

/-- Mathlib's inverse is the coproduct of the tensor inclusions. Its `lTensor`
maps agree definitionally with the underlying maps of `tensorMapCLM`. -/
private theorem prodRight_symm_toLinearMap_eq :
    (show (tensorLeftObj R C M × tensorLeftObj R C N) →ₗ[R]
      tensorLeftObj R C (TopModuleCat.of R (M × N)) from
        (TensorProduct.prodRight R R C M N).symm.toLinearMap) =
      ((tensorMapCLM R (C := C) (D := C)
        (M := M) (N := TopModuleCat.of R (M × N))
        (LinearMap.id : C →ₗ[R] C) (ContinuousLinearMap.inl R M N)).coprod
      (tensorMapCLM R (C := C) (D := C)
        (M := N) (N := TopModuleCat.of R (M × N))
        (LinearMap.id : C →ₗ[R] C) (ContinuousLinearMap.inr R M N))).toLinearMap := by
  rfl

/-- Distribute the one-sided tensor over a binary product on the right, with
exactly Mathlib's algebraic `TensorProduct.prodRight` as underlying equivalence. -/
noncomputable def tensorProdRight :
    tensorLeftObj R C (TopModuleCat.of R (M × N)) ≃L[R]
      (tensorLeftObj R C M × tensorLeftObj R C N) where
  toLinearEquiv :=
    (show tensorLeftObj R C (TopModuleCat.of R (M × N)) ≃ₗ[R]
      (tensorLeftObj R C M × tensorLeftObj R C N) from TensorProduct.prodRight R R C M N)
  continuous_toFun := by
    exact ((tensorMapCLM R (C := C) (D := C)
      (M := TopModuleCat.of R (M × N)) (N := M)
      (LinearMap.id : C →ₗ[R] C) (ContinuousLinearMap.fst R M N)).prod
      (tensorMapCLM R (C := C) (D := C)
        (M := TopModuleCat.of R (M × N)) (N := N)
        (LinearMap.id : C →ₗ[R] C) (ContinuousLinearMap.snd R M N))).continuous.congr
          (fun x ↦ (DFunLike.congr_fun (prodRight_toLinearMap_eq R C M N) x).symm)
  continuous_invFun := by
    exact ((tensorMapCLM R (C := C) (D := C)
      (M := M) (N := TopModuleCat.of R (M × N))
      (LinearMap.id : C →ₗ[R] C) (ContinuousLinearMap.inl R M N)).coprod
      (tensorMapCLM R (C := C) (D := C)
        (M := N) (N := TopModuleCat.of R (M × N))
        (LinearMap.id : C →ₗ[R] C) (ContinuousLinearMap.inr R M N))).continuous.congr
          (fun p ↦ (DFunLike.congr_fun (prodRight_symm_toLinearMap_eq R C M N) p).symm)

/-- Forgetting continuity gives Mathlib's binary-product tensor equivalence. -/
@[simp]
theorem tensorProdRight_toLinearEquiv :
    (tensorProdRight R C M N).toLinearEquiv =
      (show tensorLeftObj R C (TopModuleCat.of R (M × N)) ≃ₗ[R]
        (tensorLeftObj R C M × tensorLeftObj R C N) from
          TensorProduct.prodRight R R C M N) := by
  rfl

/-- The inverse underlying equivalence is the inverse algebraic product equivalence. -/
@[simp]
theorem tensorProdRight_symm_toLinearEquiv :
    (tensorProdRight R C M N).symm.toLinearEquiv =
      (show (tensorLeftObj R C M × tensorLeftObj R C N) ≃ₗ[R]
        tensorLeftObj R C (TopModuleCat.of R (M × N)) from
          (TensorProduct.prodRight R R C M N).symm) := by
  rfl

/-- The forward underlying linear map is the algebraic product map. -/
@[simp]
theorem tensorProdRight_toLinearMap :
    (tensorProdRight R C M N).toContinuousLinearMap.toLinearMap =
      (show tensorLeftObj R C (TopModuleCat.of R (M × N)) →ₗ[R]
        (tensorLeftObj R C M × tensorLeftObj R C N) from
          (TensorProduct.prodRight R R C M N).toLinearMap) := by
  rfl

/-- The inverse underlying linear map is the inverse algebraic product map. -/
@[simp]
theorem tensorProdRight_symm_toLinearMap :
    (tensorProdRight R C M N).symm.toContinuousLinearMap.toLinearMap =
      (show (tensorLeftObj R C M × tensorLeftObj R C N) →ₗ[R]
        tensorLeftObj R C (TopModuleCat.of R (M × N)) from
          (TensorProduct.prodRight R R C M N).symm.toLinearMap) := by
  rfl

/-- The forward continuous linear map pairs the two tensor projections. -/
theorem tensorProdRight_toContinuousLinearMap :
    (tensorProdRight R C M N).toContinuousLinearMap =
      (tensorMapCLM R (C := C) (D := C)
        (M := TopModuleCat.of R (M × N)) (N := M)
        (LinearMap.id : C →ₗ[R] C) (ContinuousLinearMap.fst R M N)).prod
      (tensorMapCLM R (C := C) (D := C)
        (M := TopModuleCat.of R (M × N)) (N := N)
        (LinearMap.id : C →ₗ[R] C) (ContinuousLinearMap.snd R M N)) := by
  apply ContinuousLinearMap.coe_injective
  exact prodRight_toLinearMap_eq R C M N

/-- The inverse continuous linear map is the coproduct of the tensor inclusions. -/
theorem tensorProdRight_symm_toContinuousLinearMap :
    (tensorProdRight R C M N).symm.toContinuousLinearMap =
      (tensorMapCLM R (C := C) (D := C)
        (M := M) (N := TopModuleCat.of R (M × N))
        (LinearMap.id : C →ₗ[R] C) (ContinuousLinearMap.inl R M N)).coprod
      (tensorMapCLM R (C := C) (D := C)
        (M := N) (N := TopModuleCat.of R (M × N))
        (LinearMap.id : C →ₗ[R] C) (ContinuousLinearMap.inr R M N)) := by
  apply ContinuousLinearMap.coe_injective
  exact prodRight_symm_toLinearMap_eq R C M N

/-- On every tensor, distribution agrees with the algebraic equivalence. -/
theorem tensorProdRight_apply (x : tensorLeftObj R C (TopModuleCat.of R (M × N))) :
    tensorProdRight R C M N x = TensorProduct.prodRight R R C M N x := by
  rfl

/-- On every pair, inverse distribution agrees with the algebraic inverse. -/
theorem tensorProdRight_symm_apply (p : tensorLeftObj R C M × tensorLeftObj R C N) :
    (tensorProdRight R C M N).symm p =
      (TensorProduct.prodRight R R C M N).symm p := by
  rfl

/-- A pure tensor with a right pair distributes componentwise. -/
@[simp]
theorem tensorProdRight_tmul (c : C) (m : M) (n : N) :
    tensorProdRight R C M N (c ⊗ₜ[R] (m, n)) =
      (c ⊗ₜ[R] m, c ⊗ₜ[R] n) := by
  exact TensorProduct.prodRight_tmul R R C M N c (m, n)

/-- A generator on the product gives the pair of the corresponding generators. -/
@[simp]
theorem tensorProdRight_tensorGenerator_apply (c : C) (m : M) (n : N) :
    tensorProdRight R C M N
      (tensorGenerator R C (TopModuleCat.of R (M × N)) c (m, n)) =
        (tensorGenerator R C M c m, tensorGenerator R C N c n) := by
  have hsource : tensorGenerator R C (TopModuleCat.of R (M × N)) c (m, n) =
      (show tensorLeftObj R C (TopModuleCat.of R (M × N)) from c ⊗ₜ[R] (m, n)) :=
    tensorGenerator_apply R C (TopModuleCat.of R (M × N)) c (m, n)
  have hdist : tensorProdRight R C M N (c ⊗ₜ[R] (m, n)) =
      (show tensorLeftObj R C M × tensorLeftObj R C N from
        (c ⊗ₜ[R] m, c ⊗ₜ[R] n)) :=
    tensorProdRight_tmul R C M N c m n
  have htarget : (show tensorLeftObj R C M × tensorLeftObj R C N from
      (c ⊗ₜ[R] m, c ⊗ₜ[R] n)) =
        (tensorGenerator R C M c m, tensorGenerator R C N c n) :=
    congrArg₂ (fun (x : tensorLeftObj R C M) (y : tensorLeftObj R C N) ↦ (x, y))
      (tensorGenerator_apply R C M c m).symm (tensorGenerator_apply R C N c n).symm
  exact (congrArg (tensorProdRight R C M N) hsource).trans (hdist.trans htarget)

/-- Distribution after a generator is the product map of the factor generators. -/
theorem tensorProdRight_comp_tensorGenerator (c : C) :
    (tensorProdRight R C M N).toContinuousLinearMap.comp
      (tensorGenerator R C (TopModuleCat.of R (M × N)) c) =
        (tensorGenerator R C M c).prodMap (tensorGenerator R C N c) := by
  apply ContinuousLinearMap.ext
  rintro ⟨m, n⟩
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearMap.coe_prodMap', Prod.map_apply] using
      tensorProdRight_tensorGenerator_apply R C M N c m n

/-- The inverse recombines a pair of pure tensors with the same coefficient.
This is the continuous realization of Mathlib's `TensorProduct.prodRight_symm_tmul`. -/
@[simp]
theorem tensorProdRight_symm_tmul (c : C) (m : M) (n : N) :
    (tensorProdRight R C M N).symm (c ⊗ₜ[R] m, c ⊗ₜ[R] n) =
      c ⊗ₜ[R] (m, n) := by
  rw [tensorProdRight_symm_apply]
  exact TensorProduct.prodRight_symm_tmul R R C M N c m n

/-- An arbitrary pair is reconstructed by summing its two tensor inclusions. -/
theorem tensorProdRight_symm_apply_pair (x : tensorLeftObj R C M)
    (y : tensorLeftObj R C N) :
    (tensorProdRight R C M N).symm (x, y) =
      tensorMapCLM R (C := C) (D := C)
        (M := M) (N := TopModuleCat.of R (M × N))
        (LinearMap.id : C →ₗ[R] C) (ContinuousLinearMap.inl R M N) x +
      tensorMapCLM R (C := C) (D := C)
        (M := N) (N := TopModuleCat.of R (M × N))
        (LinearMap.id : C →ₗ[R] C) (ContinuousLinearMap.inr R M N) y := by
  simpa only [ContinuousLinearEquiv.coe_coe, ContinuousLinearMap.coprod_apply] using
    DFunLike.congr_fun (tensorProdRight_symm_toContinuousLinearMap R C M N) (x, y)

/-- Independently chosen coefficients reconstruct as two supported pure tensors. -/
theorem tensorProdRight_symm_tmul_pair (c d : C) (m : M) (n : N) :
    (tensorProdRight R C M N).symm (c ⊗ₜ[R] m, d ⊗ₜ[R] n) =
      c ⊗ₜ[R] (m, (0 : N)) + d ⊗ₜ[R] ((0 : M), n) := by
  have hinl : tensorMapCLM R (C := C) (D := C)
      (M := M) (N := TopModuleCat.of R (M × N))
      (LinearMap.id : C →ₗ[R] C) (ContinuousLinearMap.inl R M N) (c ⊗ₜ[R] m) =
        (show tensorLeftObj R C (TopModuleCat.of R (M × N)) from
          c ⊗ₜ[R] (m, (0 : N))) :=
    tensorMapCLM_tmul R (C := C) (D := C)
      (M := M) (N := TopModuleCat.of R (M × N))
      (LinearMap.id : C →ₗ[R] C) (ContinuousLinearMap.inl R M N) c m
  have hinr : tensorMapCLM R (C := C) (D := C)
      (M := N) (N := TopModuleCat.of R (M × N))
      (LinearMap.id : C →ₗ[R] C) (ContinuousLinearMap.inr R M N) (d ⊗ₜ[R] n) =
        (show tensorLeftObj R C (TopModuleCat.of R (M × N)) from
          d ⊗ₜ[R] ((0 : M), n)) :=
    tensorMapCLM_tmul R (C := C) (D := C)
      (M := N) (N := TopModuleCat.of R (M × N))
      (LinearMap.id : C →ₗ[R] C) (ContinuousLinearMap.inr R M N) d n
  exact (tensorProdRight_symm_apply_pair R C M N
    (show tensorLeftObj R C M from c ⊗ₜ[R] m)
    (show tensorLeftObj R C N from d ⊗ₜ[R] n)).trans
      (congrArg₂ (fun (x y : tensorLeftObj R C (TopModuleCat.of R (M × N))) ↦ x + y)
        hinl hinr)

/-- The first projection after distribution is the tensor of the right first projection. -/
@[simp]
theorem tensorProdRight_fst_comp :
    (ContinuousLinearMap.fst R (tensorLeftObj R C M) (tensorLeftObj R C N)).comp
      (tensorProdRight R C M N).toContinuousLinearMap =
        tensorMapCLM R (C := C) (D := C)
          (M := TopModuleCat.of R (M × N)) (N := M)
          (LinearMap.id : C →ₗ[R] C) (ContinuousLinearMap.fst R M N) := by
  rw [tensorProdRight_toContinuousLinearMap, ContinuousLinearMap.fst_comp_prod]

/-- The second projection after distribution is the tensor of the right second projection. -/
@[simp]
theorem tensorProdRight_snd_comp :
    (ContinuousLinearMap.snd R (tensorLeftObj R C M) (tensorLeftObj R C N)).comp
      (tensorProdRight R C M N).toContinuousLinearMap =
        tensorMapCLM R (C := C) (D := C)
          (M := TopModuleCat.of R (M × N)) (N := N)
          (LinearMap.id : C →ₗ[R] C) (ContinuousLinearMap.snd R M N) := by
  rw [tensorProdRight_toContinuousLinearMap, ContinuousLinearMap.snd_comp_prod]

/-- Inverse distribution after the first inclusion is the tensor of the right first inclusion. -/
@[simp]
theorem tensorProdRight_symm_comp_inl :
    (tensorProdRight R C M N).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.inl R (tensorLeftObj R C M) (tensorLeftObj R C N)) =
        tensorMapCLM R (C := C) (D := C)
          (M := M) (N := TopModuleCat.of R (M × N))
          (LinearMap.id : C →ₗ[R] C) (ContinuousLinearMap.inl R M N) := by
  rw [tensorProdRight_symm_toContinuousLinearMap, ContinuousLinearMap.coprod_comp_inl]

/-- Inverse distribution after the second inclusion is the tensor of the right second inclusion. -/
@[simp]
theorem tensorProdRight_symm_comp_inr :
    (tensorProdRight R C M N).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.inr R (tensorLeftObj R C M) (tensorLeftObj R C N)) =
        tensorMapCLM R (C := C) (D := C)
          (M := N) (N := TopModuleCat.of R (M × N))
          (LinearMap.id : C →ₗ[R] C) (ContinuousLinearMap.inr R M N) := by
  rw [tensorProdRight_symm_toContinuousLinearMap, ContinuousLinearMap.coprod_comp_inr]

/-- A pair supported in the first coordinate reconstructs by the first tensor inclusion. -/
@[simp]
theorem tensorProdRight_symm_apply_zero_right (x : tensorLeftObj R C M) :
    (tensorProdRight R C M N).symm (x, 0) =
      tensorMapCLM R (C := C) (D := C)
        (M := M) (N := TopModuleCat.of R (M × N))
        (LinearMap.id : C →ₗ[R] C) (ContinuousLinearMap.inl R M N) x := by
  rw [tensorProdRight_symm_apply_pair]
  simp only [map_zero, add_zero]

/-- A pair supported in the second coordinate reconstructs by the second tensor inclusion. -/
@[simp]
theorem tensorProdRight_symm_apply_zero_left (y : tensorLeftObj R C N) :
    (tensorProdRight R C M N).symm (0, y) =
      tensorMapCLM R (C := C) (D := C)
        (M := N) (N := TopModuleCat.of R (M × N))
        (LinearMap.id : C →ₗ[R] C) (ContinuousLinearMap.inr R M N) y := by
  rw [tensorProdRight_symm_apply_pair]
  simp only [map_zero, zero_add]

/-- Exact underlying algebraic agreement uniquely determines continuous distribution. -/
theorem tensorProdRight_unique
    (e : tensorLeftObj R C (TopModuleCat.of R (M × N)) ≃L[R]
      (tensorLeftObj R C M × tensorLeftObj R C N))
    (he : e.toLinearEquiv =
      (show tensorLeftObj R C (TopModuleCat.of R (M × N)) ≃ₗ[R]
        (tensorLeftObj R C M × tensorLeftObj R C N) from
          TensorProduct.prodRight R R C M N)) :
    e = tensorProdRight R C M N := by
  apply ContinuousLinearEquiv.toLinearEquiv_injective
  exact he.trans (tensorProdRight_toLinearEquiv R C M N).symm

/-- The forward pure-tensor formula characterizes the continuous product equivalence. -/
theorem tensorProdRight_unique_of_tmul
    (e : tensorLeftObj R C (TopModuleCat.of R (M × N)) ≃L[R]
      (tensorLeftObj R C M × tensorLeftObj R C N))
    (he : ∀ (c : C) (m : M) (n : N),
      e (c ⊗ₜ[R] (m, n)) = (c ⊗ₜ[R] m, c ⊗ₜ[R] n)) :
    e = tensorProdRight R C M N := by
  apply ContinuousLinearEquiv.coe_injective
  apply tensorLeft_ext R (C := C) (M := TopModuleCat.of R (M × N))
    (N := TopModuleCat.of R (tensorLeftObj R C M × tensorLeftObj R C N))
  rintro c ⟨m, n⟩
  have he' : e (c ⊗ₜ[R] (m, n)) =
      (show tensorLeftObj R C M × tensorLeftObj R C N from
        (c ⊗ₜ[R] m, c ⊗ₜ[R] n)) := he c m n
  have hdist : tensorProdRight R C M N (c ⊗ₜ[R] (m, n)) =
      (show tensorLeftObj R C M × tensorLeftObj R C N from
        (c ⊗ₜ[R] m, c ⊗ₜ[R] n)) := tensorProdRight_tmul R C M N c m n
  exact he'.trans hdist.symm

variable {C M N}
variable {D : ModuleCat.{uD} R} {M' : TopModuleCat.{uM'} R} {N' : TopModuleCat.{uN'} R}

set_option maxHeartbeats 400000 in
-- Allow extra elaboration budget for the bundled tensor and product carriers.
/-- Distribution is natural in an arbitrary algebraic coefficient map and two
continuous right-factor maps, with independent target carrier universes. -/
theorem tensorProdRight_naturality (f : C →ₗ[R] D) (g : M →L[R] M') (h : N →L[R] N') :
    ((tensorMapCLM R (C := C) (D := D) (M := M) (N := M') f g).prodMap
      (tensorMapCLM R (C := C) (D := D) (M := N) (N := N') f h)).comp
        (tensorProdRight R C M N).toContinuousLinearMap =
      (tensorProdRight R D M' N').toContinuousLinearMap.comp
        (tensorMapCLM R (C := C) (D := D)
          (M := TopModuleCat.of R (M × N)) (N := TopModuleCat.of R (M' × N'))
          f (g.prodMap h)) := by
  apply tensorLeft_ext R (C := C) (M := TopModuleCat.of R (M × N))
    (N := TopModuleCat.of R (tensorLeftObj R D M' × tensorLeftObj R D N'))
  rintro c ⟨m, n⟩
  have hdist : tensorProdRight R C M N (c ⊗ₜ[R] (m, n)) =
      (show tensorLeftObj R C M × tensorLeftObj R C N from
        (c ⊗ₜ[R] m, c ⊗ₜ[R] n)) := tensorProdRight_tmul R C M N c m n
  have hprod : ((tensorMapCLM R (C := C) (D := D) (M := M) (N := M') f g).prodMap
      (tensorMapCLM R (C := C) (D := D) (M := N) (N := N') f h))
      (c ⊗ₜ[R] m, c ⊗ₜ[R] n) =
        (show tensorLeftObj R D M' × tensorLeftObj R D N' from
          (f c ⊗ₜ[R] g m, f c ⊗ₜ[R] h n)) :=
    (congrFun (ContinuousLinearMap.coe_prodMap'
      (tensorMapCLM R (C := C) (D := D) (M := M) (N := M') f g)
      (tensorMapCLM R (C := C) (D := D) (M := N) (N := N') f h))
      (c ⊗ₜ[R] m, c ⊗ₜ[R] n)).trans
        (congrArg₂ (fun (x : tensorLeftObj R D M') (y : tensorLeftObj R D N') ↦ (x, y))
          (tensorMapCLM_tmul R (C := C) (D := D) (M := M) (N := M') f g c m)
          (tensorMapCLM_tmul R (C := C) (D := D) (M := N) (N := N') f h c n))
  have hmap : tensorMapCLM R (C := C) (D := D)
      (M := TopModuleCat.of R (M × N)) (N := TopModuleCat.of R (M' × N'))
      f (g.prodMap h) (c ⊗ₜ[R] (m, n)) =
      (show tensorLeftObj R D (TopModuleCat.of R (M' × N')) from
        f c ⊗ₜ[R] (g m, h n)) :=
    tensorMapCLM_tmul R (C := C) (D := D)
      (M := TopModuleCat.of R (M × N)) (N := TopModuleCat.of R (M' × N'))
      f (g.prodMap h) c (m, n)
  have hleft : (((tensorMapCLM R (C := C) (D := D) (M := M) (N := M') f g).prodMap
      (tensorMapCLM R (C := C) (D := D) (M := N) (N := N') f h)).comp
      (tensorProdRight R C M N).toContinuousLinearMap) (c ⊗ₜ[R] (m, n)) =
        (show tensorLeftObj R D M' × tensorLeftObj R D N' from
          (f c ⊗ₜ[R] g m, f c ⊗ₜ[R] h n)) :=
    (ContinuousLinearMap.comp_apply
      ((tensorMapCLM R (C := C) (D := D) (M := M) (N := M') f g).prodMap
        (tensorMapCLM R (C := C) (D := D) (M := N) (N := N') f h))
      (tensorProdRight R C M N).toContinuousLinearMap
      (show tensorLeftObj R C (TopModuleCat.of R (M × N)) from c ⊗ₜ[R] (m, n))).trans
        ((congrArg
          ((tensorMapCLM R (C := C) (D := D) (M := M) (N := M') f g).prodMap
            (tensorMapCLM R (C := C) (D := D) (M := N) (N := N') f h)) hdist).trans hprod)
  have hright : ((tensorProdRight R D M' N').toContinuousLinearMap.comp
      (tensorMapCLM R (C := C) (D := D)
        (M := TopModuleCat.of R (M × N)) (N := TopModuleCat.of R (M' × N'))
        f (g.prodMap h))) (c ⊗ₜ[R] (m, n)) =
        (show tensorLeftObj R D M' × tensorLeftObj R D N' from
          (f c ⊗ₜ[R] g m, f c ⊗ₜ[R] h n)) :=
    (ContinuousLinearMap.comp_apply (tensorProdRight R D M' N').toContinuousLinearMap
      (tensorMapCLM R (C := C) (D := D)
        (M := TopModuleCat.of R (M × N)) (N := TopModuleCat.of R (M' × N'))
        f (g.prodMap h))
      (show tensorLeftObj R C (TopModuleCat.of R (M × N)) from c ⊗ₜ[R] (m, n))).trans
        ((congrArg (tensorProdRight R D M' N') hmap).trans
          (tensorProdRight_tmul R D M' N' (f c) (g m) (h n)))
  exact hleft.trans hright.symm

end TopModuleCat

namespace TopModuleCat

variable (R : Type uR) [CommRing R] [TopologicalSpace R]

/-- Tensoring an algebraic product of coefficients with a topological right
module distributes over the product. The underlying equivalence is
`TensorProduct.prodLeft R R C D M`; no topology on the coefficients is used. -/
noncomputable def tensorProdLeft (C : ModuleCat.{uC} R) (D : ModuleCat.{uD} R)
    (M : TopModuleCat.{uM} R) :
    tensorLeftObj R (ModuleCat.of R (C × D)) M ≃L[R]
      (tensorLeftObj R C M × tensorLeftObj R D M) where
  toLinearEquiv := TensorProduct.prodLeft R R C D M
  continuous_toFun := by
    let f := (tensorMapCLM R (C := ModuleCat.of R (C × D)) (D := C)
      (M := M) (N := M) (LinearMap.fst R C D) (ContinuousLinearMap.id R M)).prod
      (tensorMapCLM R (C := ModuleCat.of R (C × D)) (D := D)
        (M := M) (N := M) (LinearMap.snd R C D) (ContinuousLinearMap.id R M))
    have heq : (TensorProduct.prodLeft R R C D M).toLinearMap = f.toLinearMap := by
      apply TensorProduct.ext'
      rintro ⟨c, d⟩ m
      exact TensorProduct.prodLeft_tmul R R C D M c d m
    exact f.continuous.congr (fun z ↦ (DFunLike.congr_fun heq z).symm)
  continuous_invFun := by
    let e : tensorLeftObj R (ModuleCat.of R (C × D)) M ≃ₗ[R]
        (tensorLeftObj R C M × tensorLeftObj R D M) :=
      TensorProduct.prodLeft R R C D M
    let l := tensorMapCLM R (C := C) (D := ModuleCat.of R (C × D))
      (M := M) (N := M) (LinearMap.inl R C D) (ContinuousLinearMap.id R M)
    let r := tensorMapCLM R (C := D) (D := ModuleCat.of R (C × D))
      (M := M) (N := M) (LinearMap.inr R C D) (ContinuousLinearMap.id R M)
    let i := l.coprod r
    have h : e.toLinearMap.comp i.toLinearMap =
        LinearMap.id (R := R) (M := tensorLeftObj R C M × tensorLeftObj R D M) := by
      apply LinearMap.prod_ext
      · apply TensorProduct.ext'
        intro c m
        have hi : i (c ⊗ₜ[R] m, 0) =
            (((c, 0) : ModuleCat.of R (C × D)) ⊗ₜ[R] m) :=
          (DFunLike.congr_fun (ContinuousLinearMap.coprod_comp_inl l r)
            (c ⊗ₜ[R] m)).trans
              (tensorMapCLM_tmul R (C := C) (D := ModuleCat.of R (C × D))
                (M := M) (N := M) (LinearMap.inl R C D) (ContinuousLinearMap.id R M) c m)
        exact (congrArg e hi).trans
          ((TensorProduct.prodLeft_tmul R R C D M c 0 m).trans
            (congrArg (fun z : tensorLeftObj R D M ↦ (c ⊗ₜ[R] m, z))
              (TensorProduct.zero_tmul (R := R) D m)))
      · apply TensorProduct.ext'
        intro d m
        have hi : i (0, d ⊗ₜ[R] m) =
            (((0, d) : ModuleCat.of R (C × D)) ⊗ₜ[R] m) :=
          (DFunLike.congr_fun (ContinuousLinearMap.coprod_comp_inr l r)
            (d ⊗ₜ[R] m)).trans
              (tensorMapCLM_tmul R (C := D) (D := ModuleCat.of R (C × D))
                (M := M) (N := M) (LinearMap.inr R C D) (ContinuousLinearMap.id R M) d m)
        exact (congrArg e hi).trans
          ((TensorProduct.prodLeft_tmul R R C D M 0 d m).trans
            (congrArg (fun z : tensorLeftObj R C M ↦ (z, d ⊗ₜ[R] m))
              (TensorProduct.zero_tmul (R := R) C m)))
    have heq : e.symm.toLinearMap = i.toLinearMap := by
      apply LinearMap.ext
      intro p
      apply e.injective
      exact (e.apply_symm_apply p).trans (DFunLike.congr_fun h p).symm
    exact i.continuous.congr (fun p ↦ (DFunLike.congr_fun heq p).symm)


/-- Forgetting continuity gives Mathlib's coefficient-product tensor equivalence. -/
theorem tensorProdLeft_toLinearEquiv
    (C : ModuleCat.{uC} R) (D : ModuleCat.{uD} R) (M : TopModuleCat.{uM} R) :
  (tensorProdLeft R C D M).toLinearEquiv =
    (show tensorLeftObj R (ModuleCat.of R (C × D)) M ≃ₗ[R]
      (tensorLeftObj R C M × tensorLeftObj R D M) from
        TensorProduct.prodLeft R R C D M) := by
  rfl

/-- The forward continuous linear map pairs the two coefficient tensor projections. -/
theorem tensorProdLeft_toContinuousLinearMap
    (C : ModuleCat.{uC} R) (D : ModuleCat.{uD} R) (M : TopModuleCat.{uM} R) :
  (tensorProdLeft R C D M).toContinuousLinearMap =
    (tensorMapCLM R (C := ModuleCat.of R (C × D)) (D := C)
      (M := M) (N := M) (LinearMap.fst R C D) (ContinuousLinearMap.id R M)).prod
    (tensorMapCLM R (C := ModuleCat.of R (C × D)) (D := D)
      (M := M) (N := M) (LinearMap.snd R C D) (ContinuousLinearMap.id R M)) := by
  apply ContinuousLinearMap.coe_injective
  apply TensorProduct.ext'
  rintro ⟨c, d⟩ m
  exact TensorProduct.prodLeft_tmul R R C D M c d m

/-- The inverse continuous linear map sums the two coefficient tensor inclusions. -/
theorem tensorProdLeft_symm_toContinuousLinearMap
    (C : ModuleCat.{uC} R) (D : ModuleCat.{uD} R) (M : TopModuleCat.{uM} R) :
  (tensorProdLeft R C D M).symm.toContinuousLinearMap =
    (tensorMapCLM R (C := C) (D := ModuleCat.of R (C × D))
      (M := M) (N := M) (LinearMap.inl R C D) (ContinuousLinearMap.id R M)).comp
      (ContinuousLinearMap.fst R (tensorLeftObj R C M) (tensorLeftObj R D M)) +
    (tensorMapCLM R (C := D) (D := ModuleCat.of R (C × D))
      (M := M) (N := M) (LinearMap.inr R C D) (ContinuousLinearMap.id R M)).comp
      (ContinuousLinearMap.snd R (tensorLeftObj R C M) (tensorLeftObj R D M)) := by
  rw [ContinuousLinearMap.comp_fst_add_comp_snd]
  let e : tensorLeftObj R (ModuleCat.of R (C × D)) M ≃ₗ[R]
      (tensorLeftObj R C M × tensorLeftObj R D M) :=
    TensorProduct.prodLeft R R C D M
  let l := tensorMapCLM R (C := C) (D := ModuleCat.of R (C × D))
    (M := M) (N := M) (LinearMap.inl R C D) (ContinuousLinearMap.id R M)
  let r := tensorMapCLM R (C := D) (D := ModuleCat.of R (C × D))
    (M := M) (N := M) (LinearMap.inr R C D) (ContinuousLinearMap.id R M)
  let i := l.coprod r
  have hinverse : (tensorProdLeft R C D M).symm.toContinuousLinearMap.toLinearMap =
      e.symm.toLinearMap :=
    congrArg (fun q : tensorLeftObj R (ModuleCat.of R (C × D)) M ≃ₗ[R]
      (tensorLeftObj R C M × tensorLeftObj R D M) ↦ q.symm.toLinearMap)
        (tensorProdLeft_toLinearEquiv R C D M)
  apply ContinuousLinearMap.coe_injective
  apply LinearMap.prod_ext
  · apply TensorProduct.ext'
    intro c m
    have hpair : (c ⊗ₜ[R] m, (0 : tensorLeftObj R D M)) =
        (c ⊗ₜ[R] m, (0 : D) ⊗ₜ[R] m) :=
      congrArg (fun z : tensorLeftObj R D M ↦
        ((show tensorLeftObj R C M from c ⊗ₜ[R] m), z))
          (TensorProduct.zero_tmul (R := R) D m).symm
    have hstock : e.symm (c ⊗ₜ[R] m, (0 : D) ⊗ₜ[R] m) =
        (((c, 0) : ModuleCat.of R (C × D)) ⊗ₜ[R] m) :=
      TensorProduct.prodLeft_symm_tmul R R C D M c 0 m
    have hleft : (tensorProdLeft R C D M).symm (c ⊗ₜ[R] m, 0) =
        (((c, 0) : ModuleCat.of R (C × D)) ⊗ₜ[R] m) :=
      (DFunLike.congr_fun hinverse (c ⊗ₜ[R] m, 0)).trans
        ((congrArg e.symm hpair).trans hstock)
    have hright : i (c ⊗ₜ[R] m, 0) =
        (((c, 0) : ModuleCat.of R (C × D)) ⊗ₜ[R] m) :=
      (DFunLike.congr_fun (ContinuousLinearMap.coprod_comp_inl l r)
        (c ⊗ₜ[R] m)).trans
          (tensorMapCLM_tmul R (C := C) (D := ModuleCat.of R (C × D))
            (M := M) (N := M) (LinearMap.inl R C D) (ContinuousLinearMap.id R M) c m)
    exact hleft.trans hright.symm
  · apply TensorProduct.ext'
    intro d m
    have hpair : ((0 : tensorLeftObj R C M), d ⊗ₜ[R] m) =
        ((0 : C) ⊗ₜ[R] m, d ⊗ₜ[R] m) :=
      congrArg (fun z : tensorLeftObj R C M ↦
        (z, (show tensorLeftObj R D M from d ⊗ₜ[R] m)))
          (TensorProduct.zero_tmul (R := R) C m).symm
    have hstock : e.symm ((0 : C) ⊗ₜ[R] m, d ⊗ₜ[R] m) =
        (((0, d) : ModuleCat.of R (C × D)) ⊗ₜ[R] m) :=
      TensorProduct.prodLeft_symm_tmul R R C D M 0 d m
    have hleft : (tensorProdLeft R C D M).symm (0, d ⊗ₜ[R] m) =
        (((0, d) : ModuleCat.of R (C × D)) ⊗ₜ[R] m) :=
      (DFunLike.congr_fun hinverse (0, d ⊗ₜ[R] m)).trans
        ((congrArg e.symm hpair).trans hstock)
    have hright : i (0, d ⊗ₜ[R] m) =
        (((0, d) : ModuleCat.of R (C × D)) ⊗ₜ[R] m) :=
      (DFunLike.congr_fun (ContinuousLinearMap.coprod_comp_inr l r)
        (d ⊗ₜ[R] m)).trans
          (tensorMapCLM_tmul R (C := D) (D := ModuleCat.of R (C × D))
            (M := M) (N := M) (LinearMap.inr R C D) (ContinuousLinearMap.id R M) d m)
    exact hleft.trans hright.symm

/-- A pure tensor with a coefficient pair distributes componentwise. -/
theorem tensorProdLeft_tmul
    (C : ModuleCat.{uC} R) (D : ModuleCat.{uD} R) (M : TopModuleCat.{uM} R)
    (c : C) (d : D) (m : M) :
  tensorProdLeft R C D M (((c,d) : ModuleCat.of R (C × D)) ⊗ₜ[R] m) =
    (c ⊗ₜ[R] m, d ⊗ₜ[R] m) := by
  exact TensorProduct.prodLeft_tmul R R C D M c d m

/-- Distribution after a product-coefficient generator pairs the factor generators. -/
theorem tensorProdLeft_comp_tensorGenerator
    (C : ModuleCat.{uC} R) (D : ModuleCat.{uD} R) (M : TopModuleCat.{uM} R) (c : C) (d : D) :
  (tensorProdLeft R C D M).toContinuousLinearMap.comp
    (tensorGenerator R (ModuleCat.of R (C × D)) M (c,d)) =
      (tensorGenerator R C M c).prod (tensorGenerator R D M d) := by
  have he : (tensorProdLeft R C D M).toContinuousLinearMap.toLinearMap =
      (TensorProduct.prodLeft R R C D M).toLinearMap :=
    congrArg (fun q : tensorLeftObj R (ModuleCat.of R (C × D)) M ≃ₗ[R]
      (tensorLeftObj R C M × tensorLeftObj R D M) ↦ q.toLinearMap)
        (tensorProdLeft_toLinearEquiv R C D M)
  have hsource : (tensorGenerator R (ModuleCat.of R (C × D)) M (c, d)).toLinearMap =
      (TensorProduct.mk R (ModuleCat.of R (C × D)) M) (c, d) :=
    tensorGenerator_toLinearMap R (ModuleCat.of R (C × D)) M (c, d)
  have htarget : ((tensorGenerator R C M c).prod
      (tensorGenerator R D M d)).toLinearMap =
        ((TensorProduct.mk R C M) c).prod ((TensorProduct.mk R D M) d) :=
    congrArg₂ (fun (a : M →ₗ[R] tensorLeftObj R C M)
      (b : M →ₗ[R] tensorLeftObj R D M) ↦ a.prod b)
      (tensorGenerator_toLinearMap R C M c) (tensorGenerator_toLinearMap R D M d)
  have hraw : (TensorProduct.prodLeft R R C D M).toLinearMap.comp
      ((TensorProduct.mk R (ModuleCat.of R (C × D)) M) (c, d)) =
        ((TensorProduct.mk R C M) c).prod ((TensorProduct.mk R D M) d) := by
    apply LinearMap.ext
    intro m
    exact TensorProduct.prodLeft_tmul R R C D M c d m
  apply ContinuousLinearMap.coe_injective
  exact (ContinuousLinearMap.toLinearMap_comp
    (tensorProdLeft R C D M).toContinuousLinearMap
    (tensorGenerator R (ModuleCat.of R (C × D)) M (c, d))).trans
      ((congrArg₂ (fun
        (a : tensorLeftObj R (ModuleCat.of R (C × D)) M →ₗ[R]
          (tensorLeftObj R C M × tensorLeftObj R D M))
        (b : M →ₗ[R] tensorLeftObj R (ModuleCat.of R (C × D)) M) ↦ a.comp b)
          he hsource).trans (hraw.trans htarget.symm))

/-- Inverse distribution reconstructs an arbitrary pair by summing its coefficient inclusions. -/
theorem tensorProdLeft_symm_apply_pair
    (C : ModuleCat.{uC} R) (D : ModuleCat.{uD} R) (M : TopModuleCat.{uM} R)
    (x : tensorLeftObj R C M) (y : tensorLeftObj R D M) :
  (tensorProdLeft R C D M).symm (x,y) =
    tensorMapCLM R (C := C) (D := ModuleCat.of R (C × D))
      (M := M) (N := M) (LinearMap.inl R C D) (ContinuousLinearMap.id R M) x +
    tensorMapCLM R (C := D) (D := ModuleCat.of R (C × D))
      (M := M) (N := M) (LinearMap.inr R C D) (ContinuousLinearMap.id R M) y := by
  simpa only [ContinuousLinearEquiv.coe_coe, add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd'] using
      DFunLike.congr_fun (tensorProdLeft_symm_toContinuousLinearMap R C D M) (x, y)

/-- The first projection after distribution is the tensor of the first coefficient projection. -/
theorem tensorProdLeft_fst_comp
    (C : ModuleCat.{uC} R) (D : ModuleCat.{uD} R) (M : TopModuleCat.{uM} R) :
  (ContinuousLinearMap.fst R (tensorLeftObj R C M) (tensorLeftObj R D M)).comp
    (tensorProdLeft R C D M).toContinuousLinearMap =
      tensorMapCLM R (C := ModuleCat.of R (C × D)) (D := C)
        (M := M) (N := M) (LinearMap.fst R C D) (ContinuousLinearMap.id R M) := by
  rw [tensorProdLeft_toContinuousLinearMap, ContinuousLinearMap.fst_comp_prod]

/-- The second projection after distribution is the tensor of the second coefficient projection. -/
theorem tensorProdLeft_snd_comp
    (C : ModuleCat.{uC} R) (D : ModuleCat.{uD} R) (M : TopModuleCat.{uM} R) :
  (ContinuousLinearMap.snd R (tensorLeftObj R C M) (tensorLeftObj R D M)).comp
    (tensorProdLeft R C D M).toContinuousLinearMap =
      tensorMapCLM R (C := ModuleCat.of R (C × D)) (D := D)
        (M := M) (N := M) (LinearMap.snd R C D) (ContinuousLinearMap.id R M) := by
  rw [tensorProdLeft_toContinuousLinearMap, ContinuousLinearMap.snd_comp_prod]

/-- Inverse distribution after the first inclusion is the tensor of the first coefficient
inclusion. -/
theorem tensorProdLeft_symm_comp_inl
    (C : ModuleCat.{uC} R) (D : ModuleCat.{uD} R) (M : TopModuleCat.{uM} R) :
  (tensorProdLeft R C D M).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inl R (tensorLeftObj R C M) (tensorLeftObj R D M)) =
      tensorMapCLM R (C := C) (D := ModuleCat.of R (C × D))
        (M := M) (N := M) (LinearMap.inl R C D) (ContinuousLinearMap.id R M) := by
  rw [tensorProdLeft_symm_toContinuousLinearMap,
    ContinuousLinearMap.comp_fst_add_comp_snd, ContinuousLinearMap.coprod_comp_inl]

/-- Inverse distribution after the second inclusion is the tensor of the second coefficient
inclusion. -/
theorem tensorProdLeft_symm_comp_inr
    (C : ModuleCat.{uC} R) (D : ModuleCat.{uD} R) (M : TopModuleCat.{uM} R) :
  (tensorProdLeft R C D M).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inr R (tensorLeftObj R C M) (tensorLeftObj R D M)) =
      tensorMapCLM R (C := D) (D := ModuleCat.of R (C × D))
        (M := M) (N := M) (LinearMap.inr R C D) (ContinuousLinearMap.id R M) := by
  rw [tensorProdLeft_symm_toContinuousLinearMap,
    ContinuousLinearMap.comp_fst_add_comp_snd, ContinuousLinearMap.coprod_comp_inr]

/-- A pair supported in the first component reconstructs by the first coefficient inclusion. -/
theorem tensorProdLeft_symm_apply_zero_right
    (C : ModuleCat.{uC} R) (D : ModuleCat.{uD} R) (M : TopModuleCat.{uM} R)
    (x : tensorLeftObj R C M) :
  (tensorProdLeft R C D M).symm (x,0) =
    tensorMapCLM R (C := C) (D := ModuleCat.of R (C × D))
      (M := M) (N := M) (LinearMap.inl R C D) (ContinuousLinearMap.id R M) x := by
  rw [tensorProdLeft_symm_apply_pair]
  simp only [map_zero, add_zero]

/-- A pair supported in the second component reconstructs by the second coefficient inclusion. -/
theorem tensorProdLeft_symm_apply_zero_left
    (C : ModuleCat.{uC} R) (D : ModuleCat.{uD} R) (M : TopModuleCat.{uM} R)
    (y : tensorLeftObj R D M) :
  (tensorProdLeft R C D M).symm (0,y) =
    tensorMapCLM R (C := D) (D := ModuleCat.of R (C × D))
      (M := M) (N := M) (LinearMap.inr R C D) (ContinuousLinearMap.id R M) y := by
  rw [tensorProdLeft_symm_apply_pair]
  simp only [map_zero, zero_add]

/-- Inverse distribution recombines pure tensors with the same right input. -/
theorem tensorProdLeft_symm_tmul
    (C : ModuleCat.{uC} R) (D : ModuleCat.{uD} R) (M : TopModuleCat.{uM} R)
    (c : C) (d : D) (m : M) :
  (tensorProdLeft R C D M).symm (c ⊗ₜ[R] m, d ⊗ₜ[R] m) =
    (((c,d) : ModuleCat.of R (C × D)) ⊗ₜ[R] m) := by
  exact TensorProduct.prodLeft_symm_tmul R R C D M c d m

/-- Independently chosen right inputs reconstruct as two coefficient-supported pure tensors. -/
theorem tensorProdLeft_symm_tmul_pair
    (C : ModuleCat.{uC} R) (D : ModuleCat.{uD} R) (M : TopModuleCat.{uM} R)
    (c : C) (d : D) (m n : M) :
  (tensorProdLeft R C D M).symm (c ⊗ₜ[R] m, d ⊗ₜ[R] n) =
    (((c,0) : ModuleCat.of R (C × D)) ⊗ₜ[R] m) +
    (((0,d) : ModuleCat.of R (C × D)) ⊗ₜ[R] n) := by
  have hinl : tensorMapCLM R (C := C) (D := ModuleCat.of R (C × D))
      (M := M) (N := M) (LinearMap.inl R C D) (ContinuousLinearMap.id R M)
      (show tensorLeftObj R C M from c ⊗ₜ[R] m) =
        (show tensorLeftObj R (ModuleCat.of R (C × D)) M from
          ((c, 0) : ModuleCat.of R (C × D)) ⊗ₜ[R] m) :=
    (tensorMapCLM_apply R (C := C) (D := ModuleCat.of R (C × D))
      (M := M) (N := M) (LinearMap.inl R C D) (ContinuousLinearMap.id R M)
      (show tensorLeftObj R C M from c ⊗ₜ[R] m)).trans
        (TensorProduct.map_tmul (LinearMap.inl R C D)
          (ContinuousLinearMap.id R M).toLinearMap c m)
  have hinr : tensorMapCLM R (C := D) (D := ModuleCat.of R (C × D))
      (M := M) (N := M) (LinearMap.inr R C D) (ContinuousLinearMap.id R M)
      (show tensorLeftObj R D M from d ⊗ₜ[R] n) =
        (show tensorLeftObj R (ModuleCat.of R (C × D)) M from
          ((0, d) : ModuleCat.of R (C × D)) ⊗ₜ[R] n) :=
    (tensorMapCLM_apply R (C := D) (D := ModuleCat.of R (C × D))
      (M := M) (N := M) (LinearMap.inr R C D) (ContinuousLinearMap.id R M)
      (show tensorLeftObj R D M from d ⊗ₜ[R] n)).trans
        (TensorProduct.map_tmul (LinearMap.inr R C D)
          (ContinuousLinearMap.id R M).toLinearMap d n)
  exact (tensorProdLeft_symm_apply_pair R C D M
    (show tensorLeftObj R C M from c ⊗ₜ[R] m)
    (show tensorLeftObj R D M from d ⊗ₜ[R] n)).trans
      (congrArg₂ (fun (x y : tensorLeftObj R (ModuleCat.of R (C × D)) M) ↦ x + y)
        hinl hinr)

/-- Underlying algebraic agreement characterizes coefficient-product distribution. -/
theorem tensorProdLeft_unique
    (C : ModuleCat.{uC} R) (D : ModuleCat.{uD} R) (M : TopModuleCat.{uM} R)
    (e : tensorLeftObj R (ModuleCat.of R (C × D)) M ≃L[R]
      (tensorLeftObj R C M × tensorLeftObj R D M))
    (he : e.toLinearEquiv =
      (show tensorLeftObj R (ModuleCat.of R (C × D)) M ≃ₗ[R]
        (tensorLeftObj R C M × tensorLeftObj R D M) from
          TensorProduct.prodLeft R R C D M)) :
  e = tensorProdLeft R C D M := by
  apply ContinuousLinearEquiv.toLinearEquiv_injective
  exact he.trans (tensorProdLeft_toLinearEquiv R C D M).symm

/-- The formula on every pure tensor characterizes coefficient-product distribution. -/
theorem tensorProdLeft_unique_of_tmul
    (C : ModuleCat.{uC} R) (D : ModuleCat.{uD} R) (M : TopModuleCat.{uM} R)
    (e : tensorLeftObj R (ModuleCat.of R (C × D)) M ≃L[R]
      (tensorLeftObj R C M × tensorLeftObj R D M))
    (he : ∀ (c : C) (d : D) (m : M),
      e (((c, d) : ModuleCat.of R (C × D)) ⊗ₜ[R] m) =
        (c ⊗ₜ[R] m, d ⊗ₜ[R] m)) :
  e = tensorProdLeft R C D M := by
  apply ContinuousLinearEquiv.coe_injective
  apply tensorLeft_ext R (C := ModuleCat.of R (C × D)) (M := M)
    (N := TopModuleCat.of R (tensorLeftObj R C M × tensorLeftObj R D M))
  rintro ⟨c, d⟩ m
  exact (he c d m).trans (tensorProdLeft_tmul R C D M c d m).symm

/-- Distribution is natural in both algebraic coefficient maps and a continuous right-factor map. -/
theorem tensorProdLeft_naturality
    {C : ModuleCat.{uC} R} {D : ModuleCat.{uD} R} {M : TopModuleCat.{uM} R}
    {C' : ModuleCat.{uM'} R} {D' : ModuleCat.{uN'} R} {N : TopModuleCat.{uN} R}
    (f : C →ₗ[R] C') (g : D →ₗ[R] D') (h : M →L[R] N) :
  ((tensorMapCLM R (C := C) (D := C') (M := M) (N := N) f h).prodMap
    (tensorMapCLM R (C := D) (D := D') (M := M) (N := N) g h)).comp
      (tensorProdLeft R C D M).toContinuousLinearMap =
    (tensorProdLeft R C' D' N).toContinuousLinearMap.comp
      (tensorMapCLM R (C := ModuleCat.of R (C × D))
        (D := ModuleCat.of R (C' × D')) (M := M) (N := N) (f.prodMap g) h) := by
  apply tensorLeft_ext R (C := ModuleCat.of R (C × D)) (M := M)
    (N := TopModuleCat.of R (tensorLeftObj R C' N × tensorLeftObj R D' N))
  rintro ⟨c, d⟩ m
  have hdist : tensorProdLeft R C D M
      (show tensorLeftObj R (ModuleCat.of R (C × D)) M from
        ((c, d) : ModuleCat.of R (C × D)) ⊗ₜ[R] m) =
        (show tensorLeftObj R C M × tensorLeftObj R D M from
          (c ⊗ₜ[R] m, d ⊗ₜ[R] m)) :=
    tensorProdLeft_tmul R C D M c d m
  have hprod : ((tensorMapCLM R (C := C) (D := C') (M := M) (N := N) f h).prodMap
      (tensorMapCLM R (C := D) (D := D') (M := M) (N := N) g h))
      (c ⊗ₜ[R] m, d ⊗ₜ[R] m) =
        (show tensorLeftObj R C' N × tensorLeftObj R D' N from
          (f c ⊗ₜ[R] h m, g d ⊗ₜ[R] h m)) :=
    (congrFun (ContinuousLinearMap.coe_prodMap'
      (tensorMapCLM R (C := C) (D := C') (M := M) (N := N) f h)
      (tensorMapCLM R (C := D) (D := D') (M := M) (N := N) g h))
      (c ⊗ₜ[R] m, d ⊗ₜ[R] m)).trans
        (congrArg₂ (fun (x : tensorLeftObj R C' N) (y : tensorLeftObj R D' N) ↦ (x, y))
          ((tensorMapCLM_apply R (C := C) (D := C') (M := M) (N := N) f h
            (show tensorLeftObj R C M from c ⊗ₜ[R] m)).trans
              (TensorProduct.map_tmul f h.toLinearMap c m))
          ((tensorMapCLM_apply R (C := D) (D := D') (M := M) (N := N) g h
            (show tensorLeftObj R D M from d ⊗ₜ[R] m)).trans
              (TensorProduct.map_tmul g h.toLinearMap d m)))
  have hmap : tensorMapCLM R (C := ModuleCat.of R (C × D))
      (D := ModuleCat.of R (C' × D')) (M := M) (N := N) (f.prodMap g) h
      (show tensorLeftObj R (ModuleCat.of R (C × D)) M from
        ((c, d) : ModuleCat.of R (C × D)) ⊗ₜ[R] m) =
        (show tensorLeftObj R (ModuleCat.of R (C' × D')) N from
          ((f c, g d) : ModuleCat.of R (C' × D')) ⊗ₜ[R] h m) :=
    (tensorMapCLM_apply R (C := ModuleCat.of R (C × D))
      (D := ModuleCat.of R (C' × D')) (M := M) (N := N) (f.prodMap g) h
      (show tensorLeftObj R (ModuleCat.of R (C × D)) M from
        ((c, d) : ModuleCat.of R (C × D)) ⊗ₜ[R] m)).trans
          (TensorProduct.map_tmul (f.prodMap g) h.toLinearMap (c, d) m)
  have hleft : (((tensorMapCLM R (C := C) (D := C') (M := M) (N := N) f h).prodMap
      (tensorMapCLM R (C := D) (D := D') (M := M) (N := N) g h)).comp
      (tensorProdLeft R C D M).toContinuousLinearMap)
      (show tensorLeftObj R (ModuleCat.of R (C × D)) M from
        ((c, d) : ModuleCat.of R (C × D)) ⊗ₜ[R] m) =
        (show tensorLeftObj R C' N × tensorLeftObj R D' N from
          (f c ⊗ₜ[R] h m, g d ⊗ₜ[R] h m)) :=
    (ContinuousLinearMap.comp_apply
      ((tensorMapCLM R (C := C) (D := C') (M := M) (N := N) f h).prodMap
        (tensorMapCLM R (C := D) (D := D') (M := M) (N := N) g h))
      (tensorProdLeft R C D M).toContinuousLinearMap
      (show tensorLeftObj R (ModuleCat.of R (C × D)) M from
        ((c, d) : ModuleCat.of R (C × D)) ⊗ₜ[R] m)).trans
          ((congrArg
            ((tensorMapCLM R (C := C) (D := C') (M := M) (N := N) f h).prodMap
              (tensorMapCLM R (C := D) (D := D') (M := M) (N := N) g h)) hdist).trans hprod)
  have hright : ((tensorProdLeft R C' D' N).toContinuousLinearMap.comp
      (tensorMapCLM R (C := ModuleCat.of R (C × D))
        (D := ModuleCat.of R (C' × D')) (M := M) (N := N) (f.prodMap g) h))
      (show tensorLeftObj R (ModuleCat.of R (C × D)) M from
        ((c, d) : ModuleCat.of R (C × D)) ⊗ₜ[R] m) =
        (show tensorLeftObj R C' N × tensorLeftObj R D' N from
          (f c ⊗ₜ[R] h m, g d ⊗ₜ[R] h m)) :=
    (ContinuousLinearMap.comp_apply (tensorProdLeft R C' D' N).toContinuousLinearMap
      (tensorMapCLM R (C := ModuleCat.of R (C × D))
        (D := ModuleCat.of R (C' × D')) (M := M) (N := N) (f.prodMap g) h)
      (show tensorLeftObj R (ModuleCat.of R (C × D)) M from
        ((c, d) : ModuleCat.of R (C × D)) ⊗ₜ[R] m)).trans
          ((congrArg (tensorProdLeft R C' D' N) hmap).trans
            (tensorProdLeft_tmul R C' D' N (f c) (g d) (h m)))
  exact hleft.trans hright.symm

/-- Inverse distribution is natural in both coefficient maps and the continuous right-factor map. -/
theorem tensorProdLeft_symm_naturality
    {C : ModuleCat.{uC} R} {D : ModuleCat.{uD} R} {M : TopModuleCat.{uM} R}
    {C' : ModuleCat.{uM'} R} {D' : ModuleCat.{uN'} R} {N : TopModuleCat.{uN} R}
    (f : C →ₗ[R] C') (g : D →ₗ[R] D') (h : M →L[R] N) :
  (tensorMapCLM R (C := ModuleCat.of R (C × D))
    (D := ModuleCat.of R (C' × D')) (M := M) (N := N) (f.prodMap g) h).comp
      (tensorProdLeft R C D M).symm.toContinuousLinearMap =
    (tensorProdLeft R C' D' N).symm.toContinuousLinearMap.comp
      ((tensorMapCLM R (C := C) (D := C') (M := M) (N := N) f h).prodMap
        (tensorMapCLM R (C := D) (D := D') (M := M) (N := N) g h)) := by
  apply ContinuousLinearMap.ext
  intro p
  apply (tensorProdLeft R C' D' N).injective
  have hn := DFunLike.congr_fun (tensorProdLeft_naturality R f g h)
    ((tensorProdLeft R C D M).symm p)
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply] using hn.symm

end TopModuleCat
