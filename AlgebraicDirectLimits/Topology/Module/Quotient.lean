/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

/-!
# Continuous semilinear maps between submodule quotients

`Submodule.mapQL` bundles `Submodule.mapQ` as a continuous semilinear map for the
original quotient topologies. Its continuity follows from the quotient universal
property, without any continuity assumptions on addition or scalar multiplication.

The representative formula and commuting square characterize the induced map.
The API also records identity, composition, preservation of surjectivity, and the
quotient-map property for induced maps.
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
