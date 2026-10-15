/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicDirectLimits.Topology.Coinduced
public import Mathlib.Algebra.Module.ULift
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.Topology.Algebra.Module.Equiv

/-!
# One-sided tensor topologies

For an algebraic coefficient module `C` and a topological module `M`,
`TopModuleCat.tensorLeftObj` retains the carrier `C ⊗[R] M` and uses the finest
`R`-topological-module topology making every fixed-coefficient tensor generator
continuous. The coefficient module carries no topology.

Linear continuity out of this tensor is tested on the continuous fixed-coefficient
generators. `TopModuleCat.tensorMapCLM` realizes Mathlib's two-variable tensor map
for an algebraic map on the left and a continuous linear map on the right, with
application, identity and composition laws. `TopModuleCat.tensorMapBilinear`
bundles this construction as a bilinear operator on the two morphism spaces.
Forgetting continuity identifies the whole operator with Mathlib's
`TensorProduct.mapBilinear` at the identity ring homomorphism. No topology on the
coefficient modules or the morphism spaces is required.

The algebraic finite-basis coordinates use Mathlib's tensor-to-Finsupp equivalence
followed by its finite-function equivalence. `tensorCoordinateContinuousLinearEquiv`
realizes these coordinates as a continuous linear equivalence with the finite
product. Its inverse sums the continuous basis generators after the canonical
product projections. The type contracts in
`AlgebraicDirectLimitsTests.Topology.TensorProduct` specify the induced finite-product
topology equality, basis change, and separate compactness/Hausdorff preservation
properties. These contracts are types, not proofs or exported constructions
of those realizations.
The scalar ring need not be nontrivial, discrete or a field. Carrier and coordinate
index universes are independent.

## Implementation notes

The tensor carrier has no global topology instance. Universe raising is confined
to local generator domains. The generator family and its induced continuity data
are local to the carrier and generator constructions; their proof fields agree by
proof irrelevance. The continuity criterion concerns linear maps, not arbitrary
functions out of a final topology.

## References

The construction follows the scalar-extension ideas of the Continuous Group
Cohomology formalization by Formal Frontier Agents, including Beacon's original
topological development. Mathlib's topological-module category and coinduced
construction are due to Richard Hill and Andrew Yang; its tensor-basis API is due
to Jakob von Raumer, its Finsupp API to Johannes Hölzl, and its finite-free
chosen-basis API to Riccardo Brasca. The continuous-linear-equivalence API is due
to Jan-David Salchow, Sébastien Gouëzel, Jean Lo, Yury Kudryashov, Frédéric Dupuis
and Heather Macbeth. The module `ULift` API is due to Kim Morrison, and the tensor-map
and bilinear-map APIs to Kenny Lau and Mario Carneiro. The coinduced-topology
composition API is due to Johannes Hölzl and Mario Carneiro; the homeomorphism API
is due to Johannes Hölzl, Patrick
Massot, Sébastien Gouëzel, Zhouhang Zhou and Reid Barton.
The universe adapters reuse Mathlib's module and continuous linear equivalences
for `ULift`, rather than a separate universe-lift functor.
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct

universe uR uC uD uE uM uN uP uι uκ uI

namespace TopModuleCat

section Coinduced

variable {S : Type uR} [Ring S] [TopologicalSpace S]
variable {A : ModuleCat.{uC} S} {I : Type uI} {X : I → TopModuleCat.{uC} S}

/- Linear continuity out of the existing coinduced module, with an independently
leveled target. This is not a nonlinear final-topology assertion. -/

end Coinduced

variable (R : Type uR) [CommRing R] [TopologicalSpace R]

/-- The tensor product with the finest topological-module topology making every
map `m ↦ c ⊗ₜ[R] m` continuous. Only the right factor is topological. -/
noncomputable def tensorLeftObj (C : ModuleCat.{uC} R) (M : TopModuleCat.{uM} R) :
    TopModuleCat.{max uC uM} R := by
  letI : ContinuousAdd (ULift.{uC} M) :=
    continuousAdd_induced (ULift.moduleEquiv (R := R) (M := M)).toLinearMap
  letI : ContinuousSMul R (ULift.{uC} M) :=
    ContinuousSMul.induced (ULift.moduleEquiv (R := R) (M := M)).toLinearMap
  let X : C → TopModuleCat.{max uC uM} R := fun _ ↦ of R (ULift.{uC} M)
  let j : ∀ c : C, (X c).toModuleCat ⟶ ModuleCat.of R (TensorProduct R C M) :=
    fun c ↦ ModuleCat.ofHom
      (((TensorProduct.mk R C M) c).comp
        (ULift.moduleEquiv (R := R) (M := M)).toLinearMap)
  exact coinduced j

/-- The carrier of `tensorLeftObj` is the algebraic tensor product. -/
@[simp]
theorem coe_tensorLeftObj (C : ModuleCat.{uC} R) (M : TopModuleCat.{uM} R) :
    (tensorLeftObj R C M : Type (max uC uM)) = TensorProduct R C M := rfl

/-- On the retained algebraic carrier, the tensor topology is the coinduced
module topology for the unlifted family of fixed-coefficient tensor maps. -/
theorem tensorLeftObj_topologicalSpace (C : ModuleCat.{uC} R) (M : TopModuleCat.{uM} R) :
    (tensorLeftObj R C M).topologicalSpace =
      sInf {t : TopologicalSpace (TensorProduct R C M) |
        @ContinuousSMul R (TensorProduct R C M) _ _ t ∧
        @ContinuousAdd (TensorProduct R C M) t _ ∧
        ∀ c : C, M.topologicalSpace.coinduced ((TensorProduct.mk R C M) c) ≤ t} := by
  -- Unfold the construction only at its topology boundary.
  change sInf {t : TopologicalSpace (TensorProduct R C M) |
    @ContinuousSMul R (TensorProduct R C M) _ _ t ∧
    @ContinuousAdd (TensorProduct R C M) t _ ∧
    ∀ c : C, (inferInstance : TopologicalSpace (ULift.{uC} M)).coinduced
      (fun x : ULift.{uC} M ↦ c ⊗ₜ[R] x.down) ≤ t} = _
  have hdown : (inferInstance : TopologicalSpace (ULift.{uC} M)).coinduced
      (ULift.down : ULift.{uC} M → M) = M.topologicalSpace :=
    (ContinuousLinearEquiv.ulift (R₁ := R) (M₁ := M) :
      ULift.{uC} M ≃L[R] M).toHomeomorph.coinduced_eq
  have hgen (c : C) : (inferInstance : TopologicalSpace (ULift.{uC} M)).coinduced
      (fun x : ULift.{uC} M ↦ c ⊗ₜ[R] x.down) =
        M.topologicalSpace.coinduced ((TensorProduct.mk R C M) c) := by
    change (inferInstance : TopologicalSpace (ULift.{uC} M)).coinduced
      (((TensorProduct.mk R C M) c) ∘ ULift.down) = _
    rw [← coinduced_compose, hdown]
  simp_rw [hgen]

/- The unlifted topology contract is realized by `tensorLeftObj_topologicalSpace`. -/

/-- The continuous linear generator at a fixed coefficient. -/
noncomputable def tensorGenerator (C : ModuleCat.{uC} R) (M : TopModuleCat.{uM} R)
    (c : C) : M →L[R] tensorLeftObj R C M := by
  letI : ContinuousAdd (ULift.{uC} M) :=
    continuousAdd_induced (ULift.moduleEquiv (R := R) (M := M)).toLinearMap
  letI : ContinuousSMul R (ULift.{uC} M) :=
    ContinuousSMul.induced (ULift.moduleEquiv (R := R) (M := M)).toLinearMap
  let X : C → TopModuleCat.{max uC uM} R := fun _ ↦ of R (ULift.{uC} M)
  let j : ∀ c : C, (X c).toModuleCat ⟶ ModuleCat.of R (TensorProduct R C M) :=
    fun c ↦ ModuleCat.ofHom
      (((TensorProduct.mk R C M) c).comp
        (ULift.moduleEquiv (R := R) (M := M)).toLinearMap)
  exact (toCoinduced j c).hom.comp
    (ContinuousLinearEquiv.ulift (R₁ := R) (M₁ := M)).symm.toContinuousLinearMap

/-- The tensor generator sends `m` to `c ⊗ₜ[R] m`. -/
@[simp]
theorem tensorGenerator_apply (C : ModuleCat.{uC} R) (M : TopModuleCat.{uM} R)
    (c : C) (m : M) : tensorGenerator R C M c m = c ⊗ₜ[R] m := rfl

/-- Forgetting continuity of the generator gives Mathlib's tensor generator. -/
@[simp]
theorem tensorGenerator_toLinearMap (C : ModuleCat.{uC} R) (M : TopModuleCat.{uM} R)
    (c : C) : (tensorGenerator R C M c).toLinearMap = (TensorProduct.mk R C M) c := by
  ext m
  rfl

/-- Continuous linear maps out of the one-sided tensor are determined by pure tensors. -/
@[ext]
theorem tensorLeft_ext {C : ModuleCat.{uC} R} {M : TopModuleCat.{uM} R}
    {N : TopModuleCat.{uN} R} {f g : tensorLeftObj R C M →L[R] N}
    (h : ∀ c m, f (c ⊗ₜ[R] m) = g (c ⊗ₜ[R] m)) : f = g := by
  apply ContinuousLinearMap.coe_injective
  exact TensorProduct.ext' h

/-- A linear map out of the one-sided tensor is continuous exactly when its
composite with each continuous fixed-coefficient tensor generator is continuous.
The target has an independent carrier universe. -/
theorem continuous_tensorLeftObj_iff (C : ModuleCat.{uC} R) (M : TopModuleCat.{uM} R)
    (N : TopModuleCat.{uN} R) (f : tensorLeftObj R C M →ₗ[R] N) :
    Continuous f ↔ ∀ c : C, Continuous (fun m : M ↦ f (tensorGenerator R C M c m)) := by
  constructor
  · intro hf c
    exact hf.comp (tensorGenerator R C M c).continuous
  · intro h
    let : ContinuousAdd (ULift.{uC} M) :=
      continuousAdd_induced (ULift.moduleEquiv (R := R) (M := M)).toLinearMap
    let : ContinuousSMul R (ULift.{uC} M) :=
      ContinuousSMul.induced (ULift.moduleEquiv (R := R) (M := M)).toLinearMap
    let X : C → TopModuleCat.{max uC uM} R := fun _ ↦ of R (ULift.{uC} M)
    let j : ∀ c : C, (X c).toModuleCat ⟶ ModuleCat.of R (TensorProduct R C M) :=
      fun c ↦ ModuleCat.ofHom
        (((TensorProduct.mk R C M) c).comp
          (ULift.moduleEquiv (R := R) (M := M)).toLinearMap)
    change Continuous (show coinduced j →ₗ[R] N from f)
    apply (continuous_coinduced_iff j f).mpr
    intro c
    change Continuous (fun x : ULift.{uC} M ↦ f (c ⊗ₜ[R] x.down))
    simpa only [Function.comp_def, tensorGenerator_apply] using
      (h c).comp (continuous_uliftDown : Continuous (ULift.down : ULift.{uC} M → M))

/-- The pure-tensor form of the fixed-coefficient linear continuity criterion. -/
theorem continuous_tensorLeftObj_iff_tmul (C : ModuleCat.{uC} R)
    (M : TopModuleCat.{uM} R) (N : TopModuleCat.{uN} R)
    (f : tensorLeftObj R C M →ₗ[R] N) :
    Continuous f ↔ ∀ c : C, Continuous (fun m : M ↦ f (c ⊗ₜ[R] m)) := by
  simpa only [tensorGenerator_apply] using continuous_tensorLeftObj_iff R C M N f

/- Linear continuity is tested on fixed-coefficient generators. -/

section TensorMaps

variable {C : ModuleCat.{uC} R} {D : ModuleCat.{uD} R} {E : ModuleCat.{uE} R}
variable {M : TopModuleCat.{uM} R} {N : TopModuleCat.{uN} R} {P : TopModuleCat.{uP} R}

/-- The algebraic tensor map on the one-sided tensor carriers carries a generator
to the right-factor image in the generator at the left-factor image. -/
theorem tensorMap_tensorGenerator_apply (f : C →ₗ[R] D) (g : M →L[R] N)
    (c : C) (m : M) :
    (show tensorLeftObj R C M →ₗ[R] tensorLeftObj R D N from
      TensorProduct.map f g.toLinearMap) (tensorGenerator R C M c m) =
        tensorGenerator R D N (f c) (g m) := by
  change (TensorProduct.map f g.toLinearMap :
    TensorProduct R C M →ₗ[R] TensorProduct R D N) (c ⊗ₜ[R] m) =
      f c ⊗ₜ[R] g m
  exact TensorProduct.map_tmul f g.toLinearMap c m

/-- The continuous tensor map induced by an algebraic left-factor map and a
continuous linear right-factor map. Its underlying linear map is `TensorProduct.map`. -/
noncomputable def tensorMapCLM (f : C →ₗ[R] D) (g : M →L[R] N) :
    tensorLeftObj R C M →L[R] tensorLeftObj R D N where
  toLinearMap := TensorProduct.map f g.toLinearMap
  cont := by
    apply (continuous_tensorLeftObj_iff R C M (tensorLeftObj R D N)
      (show tensorLeftObj R C M →ₗ[R] tensorLeftObj R D N from
        TensorProduct.map f g.toLinearMap)).mpr
    intro c
    exact ((tensorGenerator R D N (f c)).continuous.comp g.continuous).congr
      (fun m ↦ (tensorMap_tensorGenerator_apply R f g c m).symm)

/-- Forgetting continuity gives exactly Mathlib's two-variable tensor map. -/
@[simp]
theorem tensorMapCLM_toLinearMap (f : C →ₗ[R] D) (g : M →L[R] N) :
    (tensorMapCLM R f g).toLinearMap = TensorProduct.map f g.toLinearMap := rfl

/-- The continuous tensor map acts by the algebraic tensor map on every tensor. -/
theorem tensorMapCLM_apply (f : C →ₗ[R] D) (g : M →L[R] N) (x : tensorLeftObj R C M) :
    tensorMapCLM R f g x = TensorProduct.map f g.toLinearMap x :=
  DFunLike.congr_fun (tensorMapCLM_toLinearMap R f g) x

/-- The continuous tensor map sends a pure tensor to the tensor of its images. -/
@[simp]
theorem tensorMapCLM_tmul (f : C →ₗ[R] D) (g : M →L[R] N) (c : C) (m : M) :
    tensorMapCLM R f g (c ⊗ₜ[R] m) = f c ⊗ₜ[R] g m := by
  change (TensorProduct.map f g.toLinearMap :
    TensorProduct R C M →ₗ[R] TensorProduct R D N) (c ⊗ₜ[R] m) =
      f c ⊗ₜ[R] g m
  exact TensorProduct.map_tmul f g.toLinearMap c m

/-- The continuous tensor map carries a tensor generator to the corresponding
right-factor image in the generator at the left-factor image. -/
@[simp]
theorem tensorMapCLM_tensorGenerator_apply (f : C →ₗ[R] D) (g : M →L[R] N)
    (c : C) (m : M) :
    tensorMapCLM R f g (tensorGenerator R C M c m) =
      tensorGenerator R D N (f c) (g m) := by
  calc
    tensorMapCLM R f g (tensorGenerator R C M c m) =
        (show tensorLeftObj R C M →ₗ[R] tensorLeftObj R D N from
          TensorProduct.map f g.toLinearMap) (tensorGenerator R C M c m) :=
      tensorMapCLM_apply R f g _
    _ = tensorGenerator R D N (f c) (g m) :=
      tensorMap_tensorGenerator_apply R f g c m

/-- The tensor map of the identity maps is the identity continuous linear map. -/
@[simp]
theorem tensorMapCLM_id :
    tensorMapCLM R (LinearMap.id : C →ₗ[R] C) (ContinuousLinearMap.id R M) =
      ContinuousLinearMap.id R (tensorLeftObj R C M) := by
  apply ContinuousLinearMap.coe_injective
  rw [tensorMapCLM_toLinearMap]
  change (TensorProduct.map (LinearMap.id : C →ₗ[R] C)
    (LinearMap.id : M →ₗ[R] M) :
    TensorProduct R C M →ₗ[R] TensorProduct R C M) = LinearMap.id
  exact TensorProduct.map_id

/-- Tensor maps preserve composition in the algebraic left and continuous right factors. -/
theorem tensorMapCLM_comp (f : C →ₗ[R] D) (f' : D →ₗ[R] E)
    (g : M →L[R] N) (g' : N →L[R] P) :
    tensorMapCLM R (f'.comp f) (g'.comp g) =
      (tensorMapCLM R f' g').comp (tensorMapCLM R f g) := by
  apply ContinuousLinearMap.coe_injective
  rw [tensorMapCLM_toLinearMap]
  change (TensorProduct.map (f'.comp f) (g'.toLinearMap.comp g.toLinearMap) :
    TensorProduct R C M →ₗ[R] TensorProduct R E P) =
      (TensorProduct.map f' g'.toLinearMap).comp (TensorProduct.map f g.toLinearMap)
  exact TensorProduct.map_comp f' g'.toLinearMap f g.toLinearMap

/-- Tensor maps preserve split retractions in both factors: tensoring a linear
inclusion and a continuous linear inclusion with their respective retractions
gives a split retraction on the one-sided tensor product. -/
theorem tensorMapCLM_comp_eq_id (f : C →ₗ[R] D) (r : D →ₗ[R] C)
    (g : M →L[R] N) (s : N →L[R] M)
    (hf : r.comp f = (LinearMap.id : C →ₗ[R] C))
    (hg : s.comp g = ContinuousLinearMap.id R M) :
    (tensorMapCLM R r s).comp (tensorMapCLM R f g) =
      ContinuousLinearMap.id R (tensorLeftObj R C M) := by
  rw [← tensorMapCLM_comp, hf, hg, tensorMapCLM_id]

/-- Exact algebraic agreement uniquely determines the continuous tensor map. -/
theorem tensorMapCLM_unique (f : C →ₗ[R] D) (g : M →L[R] N)
    (t : tensorLeftObj R C M →L[R] tensorLeftObj R D N)
    (ht : t.toLinearMap = TensorProduct.map f g.toLinearMap) : t = tensorMapCLM R f g := by
  apply ContinuousLinearMap.coe_injective
  exact ht.trans (tensorMapCLM_toLinearMap R f g).symm

/-- Every algebraic left-factor map and continuous right-factor map have a continuous
realization of their algebraic tensor map. The realization is `tensorMapCLM`. -/
theorem exists_tensorMapCLM (f : C →ₗ[R] D) (g : M →L[R] N) :
    ∃ t : tensorLeftObj R C M →L[R] tensorLeftObj R D N,
      t.toLinearMap = TensorProduct.map f g.toLinearMap :=
  ⟨tensorMapCLM R f g, tensorMapCLM_toLinearMap R f g⟩

/- Continuous realization of the two-variable algebraic tensor map. -/

/- Its pure-tensor law is specified through the exact algebraic agreement. -/

/- Identity and composition laws for continuous realizations of Mathlib's map. -/


section MapLinearity

/-- The continuous tensor map is zero when its algebraic left-factor map is zero. -/
@[simp]
theorem tensorMapCLM_zero_left (g : M →L[R] N) :
    tensorMapCLM R (0 : C →ₗ[R] D) g = 0 := by
  apply ContinuousLinearMap.coe_injective
  simp only [tensorMapCLM_toLinearMap, ContinuousLinearMap.toLinearMap_zero]
  change (TensorProduct.map (0 : C →ₗ[R] D) g.toLinearMap :
    TensorProduct R C M →ₗ[R] TensorProduct R D N) = 0
  exact TensorProduct.map_zero_left (M := C) (M₂ := D) g.toLinearMap

/-- The continuous tensor map is zero when its continuous right-factor map is zero. -/
@[simp]
theorem tensorMapCLM_zero_right (f : C →ₗ[R] D) :
    tensorMapCLM R f (0 : M →L[R] N) = 0 := by
  apply ContinuousLinearMap.coe_injective
  simp only [tensorMapCLM_toLinearMap, ContinuousLinearMap.toLinearMap_zero]
  change (TensorProduct.map f (0 : M →ₗ[R] N) :
    TensorProduct R C M →ₗ[R] TensorProduct R D N) = 0
  exact TensorProduct.map_zero_right (N := M) (N₂ := N) f

/-- Addition in the algebraic left-factor map becomes addition of continuous tensor maps. -/
theorem tensorMapCLM_add_left (f₁ f₂ : C →ₗ[R] D) (g : M →L[R] N) :
    tensorMapCLM R (f₁ + f₂) g = tensorMapCLM R f₁ g + tensorMapCLM R f₂ g := by
  apply ContinuousLinearMap.coe_injective
  simp only [tensorMapCLM_toLinearMap, ContinuousLinearMap.toLinearMap_add]
  change (TensorProduct.map (f₁ + f₂) g.toLinearMap :
    TensorProduct R C M →ₗ[R] TensorProduct R D N) =
      TensorProduct.map f₁ g.toLinearMap + TensorProduct.map f₂ g.toLinearMap
  exact TensorProduct.map_add_left f₁ f₂ g.toLinearMap

/-- Addition in the continuous right-factor map becomes addition of continuous tensor maps. -/
theorem tensorMapCLM_add_right (f : C →ₗ[R] D) (g₁ g₂ : M →L[R] N) :
    tensorMapCLM R f (g₁ + g₂) = tensorMapCLM R f g₁ + tensorMapCLM R f g₂ := by
  apply ContinuousLinearMap.coe_injective
  simp only [tensorMapCLM_toLinearMap, ContinuousLinearMap.toLinearMap_add]
  change (TensorProduct.map f (g₁.toLinearMap + g₂.toLinearMap) :
    TensorProduct R C M →ₗ[R] TensorProduct R D N) =
      TensorProduct.map f g₁.toLinearMap + TensorProduct.map f g₂.toLinearMap
  exact TensorProduct.map_add_right f g₁.toLinearMap g₂.toLinearMap

/-- Scalar multiplication in the algebraic left-factor map scales the continuous tensor map. -/
theorem tensorMapCLM_smul_left (r : R) (f : C →ₗ[R] D) (g : M →L[R] N) :
    tensorMapCLM R (r • f) g = r • tensorMapCLM R f g := by
  apply ContinuousLinearMap.coe_injective
  simp only [tensorMapCLM_toLinearMap, ContinuousLinearMap.toLinearMap_smul]
  change (TensorProduct.map (r • f) g.toLinearMap :
    TensorProduct R C M →ₗ[R] TensorProduct R D N) = r • TensorProduct.map f g.toLinearMap
  exact TensorProduct.map_smul_left r f g.toLinearMap

/-- Scalar multiplication in the continuous right-factor map scales the continuous tensor map. -/
theorem tensorMapCLM_smul_right (r : R) (f : C →ₗ[R] D) (g : M →L[R] N) :
    tensorMapCLM R f (r • g) = r • tensorMapCLM R f g := by
  apply ContinuousLinearMap.coe_injective
  simp only [tensorMapCLM_toLinearMap, ContinuousLinearMap.toLinearMap_smul]
  change (TensorProduct.map f (r • g.toLinearMap) :
    TensorProduct R C M →ₗ[R] TensorProduct R D N) = r • TensorProduct.map f g.toLinearMap
  exact TensorProduct.map_smul_right r f g.toLinearMap

/-- A finite sum of algebraic left-factor maps gives the sum of their continuous tensor maps. -/
theorem tensorMapCLM_sum_left {ι : Type uI} (s : Finset ι)
    (f : ι → C →ₗ[R] D) (g : M →L[R] N) :
    tensorMapCLM R (∑ i ∈ s, f i) g = ∑ i ∈ s, tensorMapCLM R (f i) g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, tensorMapCLM_zero_left]
  | insert i s hi ih => simp only [Finset.sum_insert hi, tensorMapCLM_add_left, ih]

/-- A finite sum of continuous right-factor maps gives the sum of their continuous tensor maps. -/
theorem tensorMapCLM_sum_right {ι : Type uI} (s : Finset ι)
    (f : C →ₗ[R] D) (g : ι → M →L[R] N) :
    tensorMapCLM R f (∑ i ∈ s, g i) = ∑ i ∈ s, tensorMapCLM R f (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, tensorMapCLM_zero_right]
  | insert i s hi ih => simp only [Finset.sum_insert hi, tensorMapCLM_add_right, ih]

end MapLinearity

/-- The continuous tensor map as a bilinear operator on coefficient linear maps
and right-factor continuous linear maps. The coefficient modules are algebraic;
no topology on either morphism space is used. -/
noncomputable def tensorMapBilinear (C : ModuleCat.{uC} R) (D : ModuleCat.{uD} R)
    (M : TopModuleCat.{uM} R) (N : TopModuleCat.{uN} R) :
    (C →ₗ[R] D) →ₗ[R] (M →L[R] N) →ₗ[R]
      tensorLeftObj R C M →L[R] tensorLeftObj R D N :=
  LinearMap.mk₂ R (tensorMapCLM R)
    (tensorMapCLM_add_left R) (tensorMapCLM_smul_left R)
    (tensorMapCLM_add_right R) (tensorMapCLM_smul_right R)

/-- Evaluating the bilinear operator gives the continuous tensor map. -/
theorem tensorMapBilinear_apply (f : C →ₗ[R] D) (g : M →L[R] N) :
    tensorMapBilinear R C D M N f g = tensorMapCLM R f g := rfl

/-- The bilinear operator sends a pure tensor to the tensor of the two images. -/
@[simp]
theorem tensorMapBilinear_tmul (f : C →ₗ[R] D) (g : M →L[R] N) (c : C) (m : M) :
    tensorMapBilinear R C D M N f g (c ⊗ₜ[R] m) = f c ⊗ₜ[R] g m := by
  rw [tensorMapBilinear_apply, tensorMapCLM_tmul]

/-- Forgetting continuity of a value of the operator gives Mathlib's tensor map. -/
@[simp]
theorem tensorMapBilinear_toLinearMap (f : C →ₗ[R] D) (g : M →L[R] N) :
    (tensorMapBilinear R C D M N f g).toLinearMap =
      TensorProduct.map f g.toLinearMap := by
  rw [tensorMapBilinear_apply, tensorMapCLM_toLinearMap]

/-- On every tensor, the bilinear operator agrees with the algebraic tensor map. -/
theorem tensorMapBilinear_apply_apply (f : C →ₗ[R] D) (g : M →L[R] N)
    (x : tensorLeftObj R C M) :
    tensorMapBilinear R C D M N f g x = TensorProduct.map f g.toLinearMap x := by
  rw [tensorMapBilinear_apply, tensorMapCLM_apply]

/-- Forgetting continuity of the whole bilinear operator is Mathlib's algebraic
operator, with the right morphism first mapped to its underlying linear map. -/
theorem tensorMapBilinear_coeLM :
    (tensorMapBilinear R C D M N).compr₂ (ContinuousLinearMap.coeLM R) =
      (TensorProduct.mapBilinear (RingHom.id R) C M D N).compl₂
        (ContinuousLinearMap.coeLM R) := by
  apply LinearMap.ext
  intro f
  apply LinearMap.ext
  intro g
  change (tensorMapBilinear R C D M N f g).toLinearMap =
    TensorProduct.map f g.toLinearMap
  exact tensorMapBilinear_toLinearMap R f g

/-- The operator takes identity maps to the identity tensor map. -/
@[simp]
theorem tensorMapBilinear_id :
    tensorMapBilinear R C C M M LinearMap.id (ContinuousLinearMap.id R M) =
      ContinuousLinearMap.id R (tensorLeftObj R C M) := by
  rw [tensorMapBilinear_apply, tensorMapCLM_id]

/-- The operator respects simultaneous composition in the two factors. -/
theorem tensorMapBilinear_comp (f : C →ₗ[R] D) (f' : D →ₗ[R] E)
    (g : M →L[R] N) (g' : N →L[R] P) :
    tensorMapBilinear R C E M P (f'.comp f) (g'.comp g) =
      (tensorMapBilinear R D E N P f' g').comp (tensorMapBilinear R C D M N f g) := by
  simp only [tensorMapBilinear_apply, tensorMapCLM_comp]

/-- The pure-tensor formula uniquely determines the bundled bilinear operator. -/
theorem tensorMapBilinear_unique
    (B : (C →ₗ[R] D) →ₗ[R] (M →L[R] N) →ₗ[R]
      tensorLeftObj R C M →L[R] tensorLeftObj R D N)
    (hB : ∀ f g c m, B f g (c ⊗ₜ[R] m) = f c ⊗ₜ[R] g m) :
    B = tensorMapBilinear R C D M N := by
  apply LinearMap.ext
  intro f
  apply LinearMap.ext
  intro g
  apply tensorLeft_ext R
  intro c m
  exact (hB f g c m).trans (tensorMapBilinear_tmul R f g c m).symm

end TensorMaps

section Coordinates

variable (C : ModuleCat.{uC} R) (M : TopModuleCat.{uM} R)
variable {ι : Type uι} [Finite ι]

/-- Algebraic finite-basis tensor coordinates, using Mathlib's tensor and Finsupp APIs. -/
noncomputable def tensorCoordinateLinearEquiv (b : Module.Basis ι R C) :
    TensorProduct R C M ≃ₗ[R] (ι → M) := by
  classical
  exact (TensorProduct.equivFinsuppOfBasisLeft b).trans
    (Finsupp.linearEquivFunOnFinite R M ι)

/-- The algebraic coordinates of a pure tensor. -/
@[simp]
theorem tensorCoordinateLinearEquiv_tmul_apply (b : Module.Basis ι R C)
    (c : C) (m : M) (i : ι) :
    tensorCoordinateLinearEquiv R C M b (c ⊗ₜ[R] m) i = b.repr c i • m := by
  classical
  simp [tensorCoordinateLinearEquiv]

/-- The algebraic coordinates of a continuous tensor generator. -/
@[simp]
theorem tensorCoordinateLinearEquiv_tensorGenerator_apply (b : Module.Basis ι R C)
    (c : C) (m : M) (i : ι) :
    tensorCoordinateLinearEquiv R C M b (tensorGenerator R C M c m) i = b.repr c i • m := by
  calc
    tensorCoordinateLinearEquiv R C M b (tensorGenerator R C M c m) i =
        tensorCoordinateLinearEquiv R C M b (c ⊗ₜ[R] m) i :=
      congrArg (fun x : tensorLeftObj R C M ↦ tensorCoordinateLinearEquiv R C M b x i)
        (tensorGenerator_apply R C M c m)
    _ = b.repr c i • m := tensorCoordinateLinearEquiv_tmul_apply R C M b c m i

/-- The inverse algebraic coordinate map is the finite sum of basis tensors. -/
theorem tensorCoordinateLinearEquiv_symm_apply [Fintype ι]
    (b : Module.Basis ι R C) (x : ι → M) :
    (tensorCoordinateLinearEquiv R C M b).symm x = ∑ i, b i ⊗ₜ[R] x i := by
  classical
  apply (tensorCoordinateLinearEquiv R C M b).injective
  ext j
  simp [tensorCoordinateLinearEquiv_tmul_apply]

/-- The inverse algebraic coordinates reconstruct a tensor in `tensorLeftObj` by
summing its continuous basis generators. -/
theorem tensorCoordinateLinearEquiv_symm_apply_tensorGenerator [Fintype ι]
    (b : Module.Basis ι R C) (x : ι → M) :
    (show tensorLeftObj R C M from (tensorCoordinateLinearEquiv R C M b).symm x) =
      ∑ i, tensorGenerator R C M (b i) (x i) := by
  classical
  change @Eq (TensorProduct R C M)
    ((tensorCoordinateLinearEquiv R C M b).symm x)
    (∑ i, (show TensorProduct R C M from tensorGenerator R C M (b i) (x i)))
  refine (tensorCoordinateLinearEquiv_symm_apply R C M b x).trans ?_
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun y : tensorLeftObj R C M ↦ (show TensorProduct R C M from y))
    (tensorGenerator_apply R C M (b i) (x i)).symm

/-- Finite-basis continuous tensor coordinates with the product topology.
The underlying linear equivalence is `tensorCoordinateLinearEquiv`. -/
noncomputable def tensorCoordinateContinuousLinearEquiv (b : Module.Basis ι R C) :
    tensorLeftObj R C M ≃L[R] (ι → M) where
  toLinearEquiv := tensorCoordinateLinearEquiv R C M b
  continuous_toFun := by
    apply (continuous_tensorLeftObj_iff_tmul R C M (TopModuleCat.of R (ι → M))
      (tensorCoordinateLinearEquiv R C M b).toLinearMap).mpr
    intro c
    apply continuous_pi
    intro i
    change Continuous (fun m : M ↦ tensorCoordinateLinearEquiv R C M b (c ⊗ₜ[R] m) i)
    exact (continuous_const.smul continuous_id : Continuous (fun m : M ↦ b.repr c i • m)).congr
      (fun m ↦ (tensorCoordinateLinearEquiv_tmul_apply R C M b c m i).symm)
  continuous_invFun := by
    classical
    let : Fintype ι := Fintype.ofFinite ι
    change Continuous (show (ι → M) → tensorLeftObj R C M from
      (tensorCoordinateLinearEquiv R C M b).invFun)
    rw [LinearEquiv.invFun_eq_symm]
    have hsum : Continuous (fun x : ι → M ↦ ∑ i, tensorGenerator R C M (b i) (x i)) := by
      apply continuous_finsetSum
      intro i _
      exact ((tensorGenerator R C M (b i)).comp
        (ContinuousLinearMap.proj (R := R) (φ := fun _ : ι ↦ M) i)).continuous
    exact hsum.congr (fun x ↦
      (tensorCoordinateLinearEquiv_symm_apply_tensorGenerator R C M b x).symm)

/-- Forgetting continuity gives the algebraic finite-basis coordinate equivalence. -/
@[simp]
theorem tensorCoordinateContinuousLinearEquiv_toLinearEquiv (b : Module.Basis ι R C) :
    (tensorCoordinateContinuousLinearEquiv R C M b).toLinearEquiv =
      tensorCoordinateLinearEquiv R C M b := by
  rfl

/-- Continuous tensor coordinates agree with the algebraic coordinates on every tensor. -/
theorem tensorCoordinateContinuousLinearEquiv_apply (b : Module.Basis ι R C)
    (x : tensorLeftObj R C M) :
    tensorCoordinateContinuousLinearEquiv R C M b x =
      tensorCoordinateLinearEquiv R C M b x := by
  exact DFunLike.congr_fun (tensorCoordinateContinuousLinearEquiv_toLinearEquiv R C M b) x

/-- The underlying linear map of the continuous coordinate map is the algebraic one. -/
@[simp]
theorem tensorCoordinateContinuousLinearEquiv_toContinuousLinearMap_toLinearMap
    (b : Module.Basis ι R C) :
    (tensorCoordinateContinuousLinearEquiv R C M b).toContinuousLinearMap.toLinearMap =
      (tensorCoordinateLinearEquiv R C M b).toLinearMap := by
  rw [ContinuousLinearEquiv.toLinearMap_toContinuousLinearMap,
    tensorCoordinateContinuousLinearEquiv_toLinearEquiv]

/-- The continuous coordinates of a pure tensor are scalar multiples of its right factor. -/
@[simp]
theorem tensorCoordinateContinuousLinearEquiv_tmul_apply (b : Module.Basis ι R C)
    (c : C) (m : M) (i : ι) :
    tensorCoordinateContinuousLinearEquiv R C M b (c ⊗ₜ[R] m) i =
      b.repr c i • m := by
  exact (congrArg (fun y : ι → M ↦ y i)
    (tensorCoordinateContinuousLinearEquiv_apply R C M b
      (show tensorLeftObj R C M from c ⊗ₜ[R] m))).trans
        (tensorCoordinateLinearEquiv_tmul_apply R C M b c m i)

/-- The continuous coordinates of a tensor generator use the coefficient's basis coordinates. -/
@[simp]
theorem tensorCoordinateContinuousLinearEquiv_tensorGenerator_apply (b : Module.Basis ι R C)
    (c : C) (m : M) (i : ι) :
    tensorCoordinateContinuousLinearEquiv R C M b
      (tensorGenerator R C M c m) i = b.repr c i • m := by
  rw [tensorCoordinateContinuousLinearEquiv_apply]
  exact tensorCoordinateLinearEquiv_tensorGenerator_apply R C M b c m i

section FiniteSums

variable [Fintype ι]

/-- The inverse continuous coordinate map reconstructs a tensor by summing basis generators. -/
theorem tensorCoordinateContinuousLinearEquiv_symm_apply (b : Module.Basis ι R C)
    (x : ι → M) :
    (tensorCoordinateContinuousLinearEquiv R C M b).symm x =
      ∑ i, tensorGenerator R C M (b i) (x i) := by
  rw [← ContinuousLinearEquiv.coe_symm_toLinearEquiv,
    tensorCoordinateContinuousLinearEquiv_toLinearEquiv]
  exact tensorCoordinateLinearEquiv_symm_apply_tensorGenerator R C M b x

/-- The inverse continuous coordinate map is the finite sum of raw basis tensors. -/
theorem tensorCoordinateContinuousLinearEquiv_symm_apply_tmul (b : Module.Basis ι R C)
    (x : ι → M) :
    (tensorCoordinateContinuousLinearEquiv R C M b).symm x =
      ∑ i, b i ⊗ₜ[R] x i := by
  change @Eq (TensorProduct R C M)
    ((tensorCoordinateLinearEquiv R C M b).symm x)
    (∑ i, b i ⊗ₜ[R] x i)
  exact tensorCoordinateLinearEquiv_symm_apply R C M b x

/-- The inverse continuous linear map is the sum of basis generators after Pi projections. -/
theorem tensorCoordinateContinuousLinearEquiv_symm_toContinuousLinearMap
    (b : Module.Basis ι R C) :
    (tensorCoordinateContinuousLinearEquiv R C M b).symm.toContinuousLinearMap =
      ∑ i, (tensorGenerator R C M (b i)).comp
        (ContinuousLinearMap.proj (R := R) (φ := fun _ : ι ↦ M) i) := by
  classical
  apply ContinuousLinearMap.ext
  intro x
  simpa only [sum_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    ContinuousLinearEquiv.coe_coe] using
      tensorCoordinateContinuousLinearEquiv_symm_apply R C M b x

end FiniteSums

/-- Exact algebraic agreement uniquely determines the continuous coordinate equivalence. -/
theorem tensorCoordinateContinuousLinearEquiv_unique (b : Module.Basis ι R C)
    (e : tensorLeftObj R C M ≃L[R] (ι → M))
    (he : e.toLinearEquiv = tensorCoordinateLinearEquiv R C M b) :
    e = tensorCoordinateContinuousLinearEquiv R C M b := by
  apply ContinuousLinearEquiv.toLinearEquiv_injective
  exact he.trans (tensorCoordinateContinuousLinearEquiv_toLinearEquiv R C M b).symm

/-- The algebraic coordinate equivalence has a unique continuous realization,
namely `tensorCoordinateContinuousLinearEquiv`. -/
theorem exists_tensorCoordinateContinuousLinearEquiv (b : Module.Basis ι R C) :
    ∃! e : tensorLeftObj R C M ≃L[R] (ι → M),
      e.toLinearEquiv = tensorCoordinateLinearEquiv R C M b := by
  refine ⟨tensorCoordinateContinuousLinearEquiv R C M b,
    tensorCoordinateContinuousLinearEquiv_toLinearEquiv R C M b, ?_⟩
  intro e he
  exact tensorCoordinateContinuousLinearEquiv_unique R C M b e he

/- Continuous coordinates must realize this precise algebraic equivalence. -/


section FiniteSums

variable [Fintype ι]


end FiniteSums

/- Finite-basis topology and separate conditional preservation properties. -/


end Coordinates

section BasisChange

variable (C : ModuleCat.{uC} R) (M : TopModuleCat.{uM} R)
variable {ι : Type uι} {κ : Type uκ} [Finite ι] [Finite κ]

/- The transition between independently indexed finite bases, with linear agreement. -/

section FiniteSums

variable [Fintype ι]


end FiniteSums


end BasisChange

/- Right-factor coordinate naturality for a continuous realization of the tensor map. -/

/- Canonical finite-free compactness and Hausdorffness contracts are independent. -/


/- The canonical continuous-coordinate contract uses Mathlib's existing finite
chosen-basis index, including over trivial rings. -/

end TopModuleCat
