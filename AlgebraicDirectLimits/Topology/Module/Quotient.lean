/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

/-!
# Continuous semilinear maps and submodule quotients

`Submodule.mapQL` bundles `Submodule.mapQ` as a continuous semilinear map for the
original quotient topologies. Its continuity follows from the quotient universal
property, without any continuity assumptions on addition or scalar multiplication.

The representative formula and commuting square characterize the induced map.
The API also records identity, composition, preservation of surjectivity, and the
quotient-map property for induced maps.

The first isomorphism equivalence identifies the quotient by the kernel of a
quotient linear map with its codomain. It retains the original topologies and
Mathlib's underlying algebraic equivalence. Its inverse is continuous by the
final-topology property, without separation or continuous module operations.

The third isomorphism equivalence identifies an iterated quotient with the quotient
by the larger submodule. It retains the original quotient topologies and is natural
for continuous semilinear maps preserving the two submodules. The construction bundles
Mathlib's `Submodule.quotientQuotientEquivQuotient`; both continuity directions
follow from the quotient universal property.
-/

@[expose] public section

universe uR uS uM uN uT uP

open Topology

namespace Submodule

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]
  {σ : R →+* S} {M : Type uM} {N : Type uN}
  [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [AddCommGroup N] [Module S N] [TopologicalSpace N]
  (p : Submodule R M) (q : Submodule S N)

/-- A quotient semilinear map induces a quotient map between submodule quotients. -/
theorem isQuotientMap_mapQ (f : M →ₛₗ[σ] N) (h : p ≤ q.comap f)
    (hf : IsQuotientMap f) : IsQuotientMap (p.mapQ q f h) := by
  apply p.isQuotientMap_mkQ.of_comp_iff.mp
  simpa only [← LinearMap.coe_comp, p.mapQ_mkQ q f (h := h)] using
    q.isQuotientMap_mkQ.comp hf

/-- The continuous semilinear map between quotients induced by a map sending `p` into `q`.
Its underlying semilinear map is exactly `Submodule.mapQ`. -/
def mapQL (f : M →SL[σ] N) (h : p ≤ q.comap f.toLinearMap) :
    M ⧸ p →SL[σ] N ⧸ q where
  toLinearMap := p.mapQ q f.toLinearMap h
  cont := continuous_quot_lift _ (q.mkQL.continuous.comp f.continuous)

variable (f : M →SL[σ] N) (h : p ≤ q.comap f.toLinearMap)

@[simp, norm_cast]
theorem toLinearMap_mapQL :
    (p.mapQL q f h).toLinearMap = p.mapQ q f.toLinearMap h := rfl

@[simp]
theorem mapQL_apply (x : M) :
    p.mapQL q f h (Quotient.mk x) = Quotient.mk (f x) := rfl

/-- The induced map commutes with the canonical quotient maps. -/
theorem mapQL_mkQL :
    (p.mapQL q f h).comp p.mkQL = q.mkQL.comp f := by
  apply ContinuousLinearMap.coe_injective
  exact p.mapQ_mkQ q f.toLinearMap (h := h)

/-- The commuting square uniquely determines the induced continuous semilinear map. -/
theorem mapQL_unique (g : M ⧸ p →SL[σ] N ⧸ q)
    (hg : g.comp p.mkQL = q.mkQL.comp f) :
    g = p.mapQL q f h := by
  apply ContinuousLinearMap.ext
  intro x
  obtain ⟨x, rfl⟩ := p.isQuotientMap_mkQL.surjective x
  exact DFunLike.congr_fun (hg.trans (p.mapQL_mkQL q f h).symm) x

/-- A surjective continuous semilinear map induces a surjection on quotients. -/
theorem mapQL_surjective (hf : Function.Surjective f) :
    Function.Surjective (p.mapQL q f h) := by
  intro y
  obtain ⟨y, rfl⟩ := q.isQuotientMap_mkQL.surjective y
  obtain ⟨x, rfl⟩ := hf y
  exact ⟨Quotient.mk x, p.mapQL_apply q f h x⟩

/-- A quotient continuous semilinear map induces a quotient map between submodule quotients. -/
theorem isQuotientMap_mapQL (hf : IsQuotientMap f) :
    IsQuotientMap (p.mapQL q f h) := by
  change IsQuotientMap (p.mapQL q f h).toLinearMap
  rw [toLinearMap_mapQL]
  exact p.isQuotientMap_mapQ q f.toLinearMap h hf

@[simp]
theorem mapQL_id
    (hi : p ≤ p.comap (LinearMap.id : M →ₗ[R] M) := (by rw [comap_id])) :
    p.mapQL p (ContinuousLinearMap.id R M) hi =
      ContinuousLinearMap.id R (M ⧸ p) := by
  apply ContinuousLinearMap.coe_injective
  exact p.mapQ_id hi

variable {T : Type uT} [Ring T] {P : Type uP}
  [AddCommGroup P] [Module T P] [TopologicalSpace P]
  {τ : S →+* T} {ρ : R →+* T} [RingHomCompTriple σ τ ρ]

/-- Passing to quotients respects composition of continuous semilinear maps. -/
theorem mapQL_comp (r : Submodule T P) (g : N →SL[τ] P)
    (hg : q ≤ r.comap g.toLinearMap)
    (hc := h.trans (comap_mono hg)) :
    p.mapQL r (g.comp f) hc =
      (q.mapQL r g hg).comp (p.mapQL q f h) := by
  apply ContinuousLinearMap.coe_injective
  exact p.mapQ_comp q r f.toLinearMap g.toLinearMap h hg hc

end Submodule

namespace Submodule

variable {R : Type uR} [Ring R] {M : Type uM}
  [AddCommGroup M] [Module R M] [TopologicalSpace M]

/-- The third isomorphism theorem for submodule quotients, with their original
quotient topologies. No continuity of the module operations is required. -/
def quotientQuotientEquivQuotientL (N P : Submodule R M) (h : N ≤ P) :
    ((M ⧸ N) ⧸ P.map N.mkQ) ≃L[R] M ⧸ P where
  toLinearEquiv := N.quotientQuotientEquivQuotient P h
  continuous_toFun := by
    apply ((P.map N.mkQ).isQuotientMap_mkQ.comp N.isQuotientMap_mkQ).continuous_iff.mpr
    change Continuous (fun x : M =>
      quotientQuotientEquivQuotientAux N P h (Quotient.mk (Quotient.mk x)))
    have heq : (fun x : M =>
        quotientQuotientEquivQuotientAux N P h (Quotient.mk (Quotient.mk x))) =
        P.mkQL := by
      funext x
      simpa only [mkQL_apply, mkQ_apply] using
        quotientQuotientEquivQuotientAux_mk_mk N P h x
    rw [heq]
    exact P.mkQL.continuous
  continuous_invFun := by
    apply P.isQuotientMap_mkQ.continuous_iff.mpr
    change Continuous ((P.map N.mkQ).mkQL ∘ N.mkQL)
    exact (P.map N.mkQ).mkQL.continuous.comp N.mkQL.continuous

variable (N P : Submodule R M) (h : N ≤ P)

/-- The underlying linear equivalence is the algebraic third isomorphism theorem. -/
@[simp, norm_cast]
theorem quotientQuotientEquivQuotientL_toLinearEquiv :
    (N.quotientQuotientEquivQuotientL P h).toLinearEquiv =
      N.quotientQuotientEquivQuotient P h := rfl

/-- The third isomorphism equivalence sends a double quotient representative to its class. -/
@[simp]
theorem quotientQuotientEquivQuotientL_mk_mk (x : M) :
    N.quotientQuotientEquivQuotientL P h (Quotient.mk (Quotient.mk x)) =
      Quotient.mk x :=
  quotientQuotientEquivQuotientAux_mk_mk N P h x

/-- The inverse sends a quotient representative to its double quotient class. -/
@[simp]
theorem quotientQuotientEquivQuotientL_symm_mk (x : M) :
    (N.quotientQuotientEquivQuotientL P h).symm (Quotient.mk x) =
      Quotient.mk (Quotient.mk x) := by
  rw [← quotientQuotientEquivQuotientL_mk_mk N P h x,
    ContinuousLinearEquiv.symm_apply_apply]

/-- The third isomorphism equivalence commutes with the canonical quotient maps. -/
theorem quotientQuotientEquivQuotientL_mkQL :
    (N.quotientQuotientEquivQuotientL P h).toContinuousLinearMap.comp
        ((P.map N.mkQ).mkQL.comp N.mkQL) = P.mkQL := by
  ext x
  exact quotientQuotientEquivQuotientL_mk_mk N P h x

/-- Values on common representatives uniquely determine the continuous linear map. -/
theorem quotientQuotientEquivQuotientL_unique
    (g : ((M ⧸ N) ⧸ P.map N.mkQ) →L[R] M ⧸ P)
    (hg : ∀ x : M, g (Quotient.mk (Quotient.mk x)) = Quotient.mk x) :
    g = (N.quotientQuotientEquivQuotientL P h).toContinuousLinearMap := by
  ext x
  induction x using Quotient.induction_on with
  | _ x =>
    induction x using Quotient.induction_on with
    | _ x => exact (hg x).trans (quotientQuotientEquivQuotientL_mk_mk N P h x).symm

variable {S : Type uS} [Ring S] {M₂ : Type uN}
  [AddCommGroup M₂] [Module S M₂] [TopologicalSpace M₂] {σ : R →+* S}

/-- An induced map on quotients preserves the images of compatible submodules. -/
theorem map_mkQ_le_comap_mapQL (N₂ P₂ : Submodule S M₂)
    (f : M →SL[σ] M₂) (hN : N ≤ N₂.comap f.toLinearMap)
    (hP : P ≤ P₂.comap f.toLinearMap) :
    P.map N.mkQ ≤ (P₂.map N₂.mkQ).comap (N.mapQL N₂ f hN).toLinearMap := by
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨f x, hP hx, rfl⟩

/-- The third isomorphism equivalence is natural for continuous semilinear maps.
The containment needed for the second quotient map follows from the two original
submodule containments. -/
theorem quotientQuotientEquivQuotientL_naturality
    (N₂ P₂ : Submodule S M₂) (h₂ : N₂ ≤ P₂)
    (f : M →SL[σ] M₂) (hN : N ≤ N₂.comap f.toLinearMap)
    (hP : P ≤ P₂.comap f.toLinearMap) :
    (N₂.quotientQuotientEquivQuotientL P₂ h₂).toContinuousLinearMap.comp
        ((P.map N.mkQ).mapQL (P₂.map N₂.mkQ) (N.mapQL N₂ f hN)
          (N.map_mkQ_le_comap_mapQL P N₂ P₂ f hN hP)) =
      (P.mapQL P₂ f hP).comp
        (N.quotientQuotientEquivQuotientL P h).toContinuousLinearMap := by
  ext x
  induction x using Quotient.induction_on with
  | _ x =>
    induction x using Quotient.induction_on with
    | _ x =>
      simp only [ContinuousLinearMap.comp_apply, mapQL_apply,
        ContinuousLinearEquiv.coe_coe, quotientQuotientEquivQuotientL_mk_mk]

end Submodule

namespace LinearMap

variable {R : Type uR} [Ring R] {M : Type uM} {N : Type uN}
  [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
  [TopologicalSpace M] [TopologicalSpace N]

/-- The first isomorphism equivalence for a quotient linear map, with the original
quotient and codomain topologies. -/
noncomputable def quotKerEquivOfIsQuotientMap
    (f : M →ₗ[R] N) (hf : IsQuotientMap f) : (M ⧸ f.ker) ≃L[R] N := by
  let e := f.quotKerEquivOfSurjective hf.surjective
  refine { toLinearEquiv := e, continuous_toFun := ?_, continuous_invFun := ?_ }
  · apply f.ker.isQuotientMap_mkQ.continuous_iff.mpr
    exact hf.continuous
  · apply hf.continuous_iff.mpr
    have heq : e.symm ∘ f = f.ker.mkQL := by
      funext x
      exact e.symm_apply_apply (Submodule.Quotient.mk x)
    change Continuous (e.symm ∘ f)
    rw [heq]
    exact f.ker.mkQL.continuous

variable (f : M →ₗ[R] N) (hf : IsQuotientMap f)

/-- The underlying linear equivalence is the algebraic first isomorphism theorem. -/
@[simp, norm_cast]
theorem quotKerEquivOfIsQuotientMap_toLinearEquiv :
    (f.quotKerEquivOfIsQuotientMap hf).toLinearEquiv =
      f.quotKerEquivOfSurjective hf.surjective := rfl

/-- A kernel-quotient representative maps to its image under the original map. -/
@[simp]
theorem quotKerEquivOfIsQuotientMap_apply_mk (x : M) :
    f.quotKerEquivOfIsQuotientMap hf (Submodule.Quotient.mk x) = f x := rfl

/-- The inverse sends an image to the class of any of its preimages. -/
@[simp]
theorem quotKerEquivOfIsQuotientMap_symm_apply (x : M) :
    (f.quotKerEquivOfIsQuotientMap hf).symm (f x) = Submodule.Quotient.mk x := by
  rw [← quotKerEquivOfIsQuotientMap_apply_mk f hf x,
    ContinuousLinearEquiv.symm_apply_apply]

/-- The first isomorphism equivalence commutes with the kernel quotient map. -/
theorem quotKerEquivOfIsQuotientMap_mkQL :
    (f.quotKerEquivOfIsQuotientMap hf).toContinuousLinearMap.comp f.ker.mkQL =
      ({ toLinearMap := f, cont := hf.continuous } : M →L[R] N) := by
  ext x
  exact quotKerEquivOfIsQuotientMap_apply_mk f hf x

/-- Values on representatives uniquely determine the induced continuous linear map. -/
theorem quotKerEquivOfIsQuotientMap_unique
    (g : (M ⧸ f.ker) →L[R] N)
    (hg : ∀ x : M, g (Submodule.Quotient.mk x) = f x) :
    g = (f.quotKerEquivOfIsQuotientMap hf).toContinuousLinearMap := by
  ext x
  induction x using Submodule.Quotient.induction_on with
  | _ x => exact (hg x).trans (quotKerEquivOfIsQuotientMap_apply_mk f hf x).symm

variable {S : Type uS} [Ring S] {M₂ : Type uT} {N₂ : Type uP}
  [AddCommGroup M₂] [AddCommGroup N₂] [Module S M₂] [Module S N₂]
  [TopologicalSpace M₂] [TopologicalSpace N₂] {σ : R →+* S}
  (g : M₂ →ₗ[S] N₂) (hg : IsQuotientMap g)
  (α : M →SL[σ] M₂) (β : N →SL[σ] N₂)

/-- The first isomorphism equivalence is natural for compatible semilinear maps.
The commuting square supplies the containment needed for the quotient map. -/
theorem quotKerEquivOfIsQuotientMap_naturality
    (hSquare : β.toLinearMap.comp f = g.comp α.toLinearMap) :
    (g.quotKerEquivOfIsQuotientMap hg).toContinuousLinearMap.comp
        (f.ker.mapQL g.ker α
          ((ker_le_ker_comp f β.toLinearMap).trans_eq
            ((congrArg ker hSquare).trans (ker_comp α.toLinearMap g)))) =
      β.comp (f.quotKerEquivOfIsQuotientMap hf).toContinuousLinearMap := by
  ext x
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    simp only [ContinuousLinearMap.comp_apply, Submodule.mapQL_apply,
      ContinuousLinearEquiv.coe_coe, quotKerEquivOfIsQuotientMap_apply_mk]
    exact (DFunLike.congr_fun hSquare x).symm

end LinearMap
