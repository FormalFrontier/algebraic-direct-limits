/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicDirectLimits.Topology.TensorProduct
public import Mathlib.LinearAlgebra.TensorProduct.Prod

/-!
# Binary products of one-sided topological tensors

`TopModuleCat.tensorProdRight` realizes Mathlib's algebraic `TensorProduct.prodRight`
as a continuous linear equivalence. Its source tensors an algebraic coefficient
module with the product of two topological modules. Its target is the ordinary
product of the two one-sided tensor objects, with the product topology and action.
The coefficient module has no topology, and all carrier universes are independent.

The characteristic API describes the underlying equivalence, generators, arbitrary
inverse reconstruction, projections, inclusions, uniqueness and naturality. The
forward continuous linear map is the product of the tensor projections; the inverse
is the coproduct of the tensor inclusions. Generic equivalence round trips and
extensionality for maps out of the tensor are supplied by the existing APIs.

## References

Mathlib's algebraic tensor-product distribution over binary products is due to
Eric Wieser. Its tensor-map and scalar-tower APIs are due to Kenny Lau and Mario
Carneiro. The one-sided topology, generators and linear continuity criterion follow
Formal Frontier Agents' topological tensor development and the Continuous Group
Cohomology formalization. Mathlib's topological-module category and coinduced
construction are due to Richard Hill and Andrew Yang. The continuous-linear-map
and equivalence APIs are due to Jan-David Salchow, Sébastien Gouëzel, Jean Lo,
Yury Kudryashov, Frédéric Dupuis and Heather Macbeth.
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
