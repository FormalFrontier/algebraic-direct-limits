/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicDirectLimits.Algebra.Colimit.Zero
public import AlgebraicDirectLimits.Order.DirectedSystem
public import Mathlib.Algebra.Group.Finsupp
import Mathlib.Data.Finsupp.Basic

/-!
# Finite-support coefficient descent in direct limits

Applying `Finsupp.mapRange.zeroHom` to the selected zero-preserving transition maps gives
a directed system of finitely supported functions. Its direct limit maps
canonically to finitely supported functions on the original direct limit.
This comparison is bijective. Every finitely supported function has a common-stage
representative with exactly its support, although an arbitrary representative
can have coefficients that become zero in the limit.
-/

@[expose] public section

universe uι uG uT uα

namespace DirectLimit

variable {ι : Type uι} [Preorder ι]
variable {G : ι → Type uG} {T : ∀ ⦃i j : ι⦄, i ≤ j → Sort uT}
variable (f : ∀ i j (h : i ≤ j), T h)
variable [∀ ⦃i j⦄ (h : i ≤ j), FunLike (T h) (G i) (G j)]
variable [∀ i, Zero (G i)]
variable (hzero : ∀ i j (h : i ≤ j), f i j h 0 = 0)

/-- The zero-preserving transition maps induced on finitely supported functions. -/
noncomputable def finsuppTransition (α : Type uα) (i j : ι) (h : i ≤ j) :
    ZeroHom (α →₀ G i) (α →₀ G j) :=
  Finsupp.mapRange.zeroHom ⟨f i j h, hzero i j h⟩

@[simp] theorem finsuppTransition_apply (α : Type uα) (i j : ι) (h : i ≤ j)
    (q : α →₀ G i) (a : α) :
    finsuppTransition f hzero α i j h q a = f i j h (q a) := by
  rfl

variable [DirectedSystem G (f · · ·)]

/-- The induced transitions satisfy the identity law. -/
@[simp] theorem finsuppTransition_self (α : Type uα) (i : ι) (q : α →₀ G i) :
    finsuppTransition f hzero α i i le_rfl q = q := by
  ext a
  exact DirectedSystem.map_self' f (q a)

/-- The induced transitions satisfy the composition law. -/
theorem finsuppTransition_comp (α : Type uα) {i j k : ι}
    (hij : i ≤ j) (hjk : j ≤ k) (q : α →₀ G i) :
    finsuppTransition f hzero α j k hjk (finsuppTransition f hzero α i j hij q) =
      finsuppTransition f hzero α i k (hij.trans hjk) q := by
  ext a
  exact DirectedSystem.map_map' f hij hjk (q a)

/-- Finitely supported functions on a zero-preserving directed system form a
    directed system using `mapRange` of the original selected maps. -/
instance finsuppDirectedSystem (α : Type uα) :
    DirectedSystem (fun i : ι ↦ α →₀ G i) (finsuppTransition f hzero α · · ·) where
  map_self := by
    intro i q
    exact finsuppTransition_self f hzero α i q
  map_map := by
    intro k j i hij hjk q
    exact finsuppTransition_comp f hzero α hij hjk q

variable [IsDirectedOrder ι] [Nonempty ι] {α : Type uα}

/-- Map coefficients from one stage into the original direct limit. -/
noncomputable def finsuppMk (i : ι) : (α →₀ G i) → (α →₀ DirectLimit G f) :=
  Finsupp.mapRange (fun x ↦ (⟦⟨i, x⟩⟧ : DirectLimit G f))
    (zero_eq_mk_of_map_zero f hzero i).symm

@[simp] theorem finsuppMk_apply (i : ι) (q : α →₀ G i) (a : α) :
    finsuppMk f hzero i q a = (⟦⟨i, q a⟩⟧ : DirectLimit G f) := by
  rfl

@[simp] theorem finsuppMk_zero (i : ι) :
    finsuppMk (α := α) f hzero i 0 = 0 := by
  exact Finsupp.mapRange_zero

/-- Stagewise coefficient maps are compatible with the induced transitions. -/
theorem finsuppMk_compat (i j : ι) (h : i ≤ j) (q : α →₀ G i) :
    finsuppMk f hzero i q =
      finsuppMk f hzero j (finsuppTransition f hzero α i j h q) := by
  ext a
  exact eq_of_le ⟨i, q a⟩ j h

/-- The canonical comparison from the direct limit of finitely supported functions
    to finitely supported functions on the original direct limit. -/
noncomputable def finsuppComparison :
    DirectLimit (fun i : ι ↦ α →₀ G i) (finsuppTransition f hzero α) →
      (α →₀ DirectLimit G f) :=
  DirectLimit.lift (finsuppTransition f hzero α)
    (finsuppMk (α := α) f hzero) (finsuppMk_compat (α := α) f hzero)

@[simp] theorem finsuppComparison_mk (i : ι) (q : α →₀ G i) :
    finsuppComparison f hzero ⟦⟨i, q⟩⟧ = finsuppMk f hzero i q := by
  rfl

theorem finsuppComparison_mk_apply (i : ι) (q : α →₀ G i) (a : α) :
    finsuppComparison f hzero ⟦⟨i, q⟩⟧ a = (⟦⟨i, q a⟩⟧ : DirectLimit G f) := by
  rfl

@[simp] theorem finsuppComparison_zero :
    finsuppComparison (α := α) f hzero 0 = 0 := by
  classical
  rw [zero_eq_mk_of_map_zero (finsuppTransition f hzero α)
    (fun i j h ↦ map_zero (finsuppTransition f hzero α i j h))
    (Classical.choice ‹Nonempty ι›), finsuppComparison_mk, finsuppMk_zero]

/-- An arbitrary representative retains precisely those supported coordinates
    whose coefficients do not become zero in the original direct limit. -/
theorem mem_support_finsuppComparison_mk (i : ι) (q : α →₀ G i) (a : α) :
    a ∈ (finsuppComparison f hzero ⟦⟨i, q⟩⟧).support ↔
      a ∈ q.support ∧ (⟦⟨i, q a⟩⟧ : DirectLimit G f) ≠ 0 := by
  rw [Finsupp.mem_support_iff, finsuppComparison_mk_apply]
  refine ⟨fun h ↦ ⟨?_, h⟩, fun h ↦ h.2⟩
  rw [Finsupp.mem_support_iff]
  intro hq
  apply h
  rw [hq, ← zero_eq_mk_of_map_zero f hzero i]

/-- Every finitely supported function descends to one stage with exactly the same
    support. The assertion concerns the existence of a suitable representative. -/
theorem exists_finsuppMk_eq_support (p : α →₀ DirectLimit G f) :
    ∃ (i : ι) (q : α →₀ G i),
      finsuppMk f hzero i q = p ∧ q.support = p.support := by
  classical
  obtain ⟨i, v, hv⟩ := exists_eq_mk_of_finite f (fun a : p.support ↦ p a)
  -- Zero represents every remaining coefficient at the same stage.
  have hp : p ∈ Set.range (finsuppMk f hzero i) := by
    rw [finsuppMk, Finsupp.range_mapRange]
    intro a
    by_cases ha : a ∈ p.support
    · exact ⟨v ⟨a, ha⟩, (hv ⟨a, ha⟩).symm⟩
    · exact ⟨0, (zero_eq_mk_of_map_zero f hzero i).symm.trans
        (Finsupp.notMem_support_iff.mp ha).symm⟩
  obtain ⟨q, hq⟩ := hp
  -- Remove any coefficients outside the desired support that vanish in the limit.
  refine ⟨i, q.filter (· ∈ p.support), ?_, ?_⟩
  · ext a
    by_cases ha : a ∈ p.support
    · simpa only [finsuppMk_apply, Finsupp.filter_apply, ite_eq_left ha] using
        congrArg (fun r : α →₀ DirectLimit G f ↦ r a) hq
    · simp only [finsuppMk_apply, Finsupp.filter_apply, ite_eq_right ha]
      exact (zero_eq_mk_of_map_zero f hzero i).symm.trans
        (Finsupp.notMem_support_iff.mp ha).symm
  · ext a
    rw [Finsupp.support_filter, Finset.mem_filter]
    refine ⟨And.right, fun ha ↦ ⟨?_, ha⟩⟩
    rw [Finsupp.mem_support_iff]
    intro hqa
    have he := congrArg (fun r : α →₀ DirectLimit G f ↦ r a) hq
    rw [finsuppMk_apply, hqa, ← zero_eq_mk_of_map_zero f hzero i] at he
    exact (Finsupp.mem_support_iff.mp ha) he.symm

/-- The canonical finite-support comparison is bijective. -/
theorem finsuppComparison_bijective :
    Function.Bijective (finsuppComparison (α := α) f hzero) := by
  classical
  constructor
  · intro x y hxy
    obtain ⟨i, q, rfl⟩ := exists_eq_mk (finsuppTransition f hzero α) x
    obtain ⟨j, r, rfl⟩ := exists_eq_mk (finsuppTransition f hzero α) y
    -- Only the finite union of supports needs a simultaneous equality witness.
    let s := q.support ∪ r.support
    have he (a : s) : (⟦⟨i, q a⟩⟧ : DirectLimit G f) = ⟦⟨j, r a⟩⟧ := by
      simpa only [finsuppComparison_mk_apply] using
        congrArg (fun p : α →₀ DirectLimit G f ↦ p a) hxy
    obtain ⟨k, hik, hjk, hk⟩ :=
      (forall_mk_eq_iff_exists_of_fixed f i j
        (fun a : s ↦ q a) (fun a : s ↦ r a)).mp he
    apply Quotient.sound
    refine ⟨k, hik, hjk, ?_⟩
    ext a
    by_cases ha : a ∈ s
    · exact hk ⟨a, ha⟩
    · have hqa : q a = 0 := Finsupp.notMem_support_iff.mp
        (fun h ↦ ha (Finset.mem_union.mpr (Or.inl h)))
      have hra : r a = 0 := Finsupp.notMem_support_iff.mp
        (fun h ↦ ha (Finset.mem_union.mpr (Or.inr h)))
      simp only [finsuppTransition_apply, hqa, hra, hzero]
  · intro p
    obtain ⟨i, q, hq, -⟩ := exists_finsuppMk_eq_support f hzero p
    exact ⟨⟦⟨i, q⟩⟧, (finsuppComparison_mk f hzero i q).trans hq⟩

/-- Finitely supported functions commute with nonempty directed limits of
    zero-preserving systems, via the canonical coefficientwise comparison. -/
noncomputable def finsuppEquiv :
    DirectLimit (fun i : ι ↦ α →₀ G i) (finsuppTransition f hzero α) ≃
      (α →₀ DirectLimit G f) :=
  Equiv.ofBijective (finsuppComparison f hzero) (finsuppComparison_bijective f hzero)

/-- The equivalence uses the canonical comparison as its forward function. -/
theorem finsuppEquiv_apply
    (x : DirectLimit (fun i : ι ↦ α →₀ G i) (finsuppTransition f hzero α)) :
    finsuppEquiv f hzero x = finsuppComparison f hzero x := by
  rfl

@[simp] theorem finsuppEquiv_mk (i : ι) (q : α →₀ G i) :
    finsuppEquiv f hzero ⟦⟨i, q⟩⟧ = finsuppMk f hzero i q := by
  rfl

theorem finsuppEquiv_mk_apply (i : ι) (q : α →₀ G i) (a : α) :
    finsuppEquiv f hzero ⟦⟨i, q⟩⟧ a = (⟦⟨i, q a⟩⟧ : DirectLimit G f) := by
  rfl

/-- The inverse takes a stagewise image to its class in the induced direct limit. -/
@[simp] theorem finsuppEquiv_symm_finsuppMk (i : ι) (q : α →₀ G i) :
    (finsuppEquiv f hzero).symm (finsuppMk f hzero i q) = ⟦⟨i, q⟩⟧ := by
  rw [← finsuppEquiv_mk f hzero i q, Equiv.symm_apply_apply]

@[simp] theorem finsuppEquiv_zero :
    finsuppEquiv (α := α) f hzero 0 = 0 := by
  exact finsuppComparison_zero f hzero

@[simp] theorem finsuppEquiv_symm_zero :
    (finsuppEquiv (α := α) f hzero).symm 0 = 0 := by
  apply (finsuppEquiv f hzero).injective
  simp only [Equiv.apply_symm_apply, finsuppEquiv_zero]

end DirectLimit
