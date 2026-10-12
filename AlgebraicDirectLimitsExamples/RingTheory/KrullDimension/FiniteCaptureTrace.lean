/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicDirectLimits.RingTheory.KrullDimension.FiniteCapture
public import Mathlib.Algebra.MvPolynomial.Variables
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.ZMod.Basic

/-!
# Finite-variable stages and proper subsemiring traces

Every finite set of polynomials in countably many variables over `ℕ` comes from one
finite-variable stage: take the union of the variables of the polynomials. No such
stage maps onto the whole polynomial semiring.

The subsemiring using only even-indexed variables is proper. The stage on the single
odd variable `1` has a proper preimage of this subsemiring, and no finite-variable
stage restricts surjectively onto it. Nevertheless, its finite subsets are captured
in one restricted stage. This gives a non-uniform-stage application of the trace
dimension inequality.

A separate trivial-semiring example checks the bottom dimension value. It illustrates
only the degenerate boundary, not the nonvacuity supplied by the polynomial example.

The polynomial variable and renaming APIs used here are from Mathlib.
-/

@[expose] public section

noncomputable section

namespace FiniteCaptureTraceExamples

open MvPolynomial

/-- The subsemiring of natural-coefficient polynomials obtained by replacing each variable
`X n` with `X (2 * n)`. -/
abbrev evenVariables : Subsemiring (MvPolynomial ℕ ℕ) :=
  (rename (fun n : ℕ => 2 * n)).toRingHom.rangeS

/-- Membership in the even-variable subsemiring means being the renaming of a polynomial
along the map `n ↦ 2 * n`. -/
@[simp]
theorem mem_evenVariables_iff {p : MvPolynomial ℕ ℕ} :
    p ∈ evenVariables ↔ ∃ q : MvPolynomial ℕ ℕ, rename (fun n : ℕ => 2 * n) q = p :=
  RingHom.mem_rangeS

/-- One finite-variable stage captures an entire finite family of polynomials. -/
theorem finite_subset_range_rename (E : Set (MvPolynomial ℕ ℕ)) (hE : E.Finite) :
    ∃ s : Finset ℕ, E ⊆ Set.range (rename (Subtype.val : s → ℕ)).toRingHom := by
  classical
  let s := hE.toFinset.biUnion MvPolynomial.vars
  refine ⟨s, fun p hp => ?_⟩
  obtain ⟨q, hq⟩ := exists_rename_eq_of_vars_subset_range p
    (Subtype.val : s → ℕ) Subtype.val_injective (fun n hn =>
      ⟨⟨n, Finset.mem_biUnion.mpr ⟨p, hE.mem_toFinset.mpr hp, hn⟩⟩, rfl⟩)
  exact ⟨q, hq⟩

private theorem variable_not_in_stage_range (s : Finset ℕ) (n : ℕ) (hn : n ∉ s) :
    (X n : MvPolynomial ℕ ℕ) ∉
      Set.range (rename (Subtype.val : s → ℕ)).toRingHom := by
  rintro ⟨p, hp⟩
  change rename (Subtype.val : s → ℕ) p = X n at hp
  have hv : n ∈ (rename (Subtype.val : s → ℕ) p).vars := by
    rw [hp]
    simp
  obtain ⟨j, _, hj⟩ := mem_vars_rename (Subtype.val : s → ℕ) p hv
  exact hn (hj ▸ j.property)

/-- Each finite-variable stage misses a variable, so no stage is surjective. -/
theorem finite_variable_stage_not_surjective (s : Finset ℕ) :
    ¬ Function.Surjective (rename (R := ℕ) (Subtype.val : s → ℕ)).toRingHom := by
  obtain ⟨n, hn⟩ := s.exists_notMem
  intro h
  exact variable_not_in_stage_range s n hn (h (X n))

private theorem odd_variable_not_mem_evenVariables :
    (X 1 : MvPolynomial ℕ ℕ) ∉ evenVariables := by
  rw [mem_evenVariables_iff]
  rintro ⟨p, hp⟩
  have hv : 1 ∈ (rename (fun n : ℕ => 2 * n) p).vars := by
    rw [hp]
    simp
  obtain ⟨n, _, hn⟩ := mem_vars_rename (fun n : ℕ => 2 * n) p hv
  simpa [Nat.mul_mod] using congrArg (fun k : ℕ => k % 2) hn

/-- The even-variable subsemiring is proper, and its preimage at an odd-variable stage
is also proper. Thus a preimage trace need not be the entire stage semiring. -/
theorem even_variables_and_odd_trace_proper :
    evenVariables < ⊤ ∧
      evenVariables.comap
        (rename (Subtype.val : ({1} : Finset ℕ) → ℕ)).toRingHom < ⊤ := by
  constructor
  · apply lt_top_iff_ne_top.mpr
    intro h
    apply odd_variable_not_mem_evenVariables
    rw [h]
    trivial
  · apply lt_top_iff_ne_top.mpr
    intro h
    have hx : (X (⟨1, by simp⟩ : ({1} : Finset ℕ)) :
        MvPolynomial ({1} : Finset ℕ) ℕ) ∈
        evenVariables.comap
          (rename (Subtype.val : ({1} : Finset ℕ) → ℕ)).toRingHom := by
      rw [h]
      trivial
    apply odd_variable_not_mem_evenVariables
    change rename (Subtype.val : ({1} : Finset ℕ) → ℕ)
      (X (⟨1, by simp⟩ : ({1} : Finset ℕ))) ∈ evenVariables at hx
    simpa only [rename_X] using hx

/-- Finite subsets of the even-variable subsemiring are captured in one restricted stage,
by finite image and the canonical restriction range identity. -/
theorem finite_subset_range_even_variable_restrictions
    (E : Set evenVariables) (hE : E.Finite) :
    ∃ s : Finset ℕ, E ⊆ Set.range
      ((rename (Subtype.val : s → ℕ)).toRingHom.restrict
        (evenVariables.comap (rename (Subtype.val : s → ℕ)).toRingHom)
        evenVariables (fun _ hx => hx)) := by
  obtain ⟨s, hs⟩ := finite_subset_range_rename
    (Subtype.val '' E) (hE.image Subtype.val)
  refine ⟨s, ?_⟩
  rw [RingHom.range_restrict_comap]
  exact Set.image_subset_iff.mp hs

/-- No restricted finite-variable stage captures all even-variable polynomials. -/
theorem no_finite_stage_surjects_onto_even_variables (s : Finset ℕ) :
    ¬ Function.Surjective
      ((rename (Subtype.val : s → ℕ)).toRingHom.restrict
        (evenVariables.comap (rename (Subtype.val : s → ℕ)).toRingHom)
        evenVariables (fun _ hx => hx)) := by
  let n := s.sup id + 1
  have hn : 2 * n ∉ s := by
    intro h
    have hle : 2 * n ≤ s.sup id := Finset.le_sup (f := id) h
    have hlt : s.sup id < n := Nat.lt_succ_self (s.sup id)
    exact (not_lt_of_ge hle) (hlt.trans_le (Nat.le_mul_of_pos_left n (by decide)))
  let a : evenVariables := ⟨X (2 * n), mem_evenVariables_iff.mpr ⟨X n, rename_X _ _⟩⟩
  intro h
  obtain ⟨p, hp⟩ := h a
  apply variable_not_in_stage_range s (2 * n) hn
  exact ⟨(p : MvPolynomial s ℕ), congrArg Subtype.val hp⟩

/-- The trace dimension inequality applies to the proper even-variable subsemiring,
with finite capture established by the polynomial variable union. -/
theorem even_variable_dimension_bound :
    ringKrullDim evenVariables ≤ ⨆ s : Finset ℕ,
      ringKrullDim
        (evenVariables.comap (rename (Subtype.val : s → ℕ)).toRingHom) :=
  ringKrullDim_subsemiring_le_iSup_comap_of_finite_subset_range
    (R := fun s : Finset ℕ => MvPolynomial s ℕ)
    (fun s => (rename (Subtype.val : s → ℕ)).toRingHom)
    evenVariables finite_subset_range_rename

/-- The singleton identity family on a trivial semiring satisfies finite capture;
its top subsemiring has dimension `⊥`, not dimension zero. -/
theorem trivial_trace_bottom_bound :
    ringKrullDim (⊤ : Subsemiring (ZMod 1)) = ⊥ ∧
      ringKrullDim (⊤ : Subsemiring (ZMod 1)) ≤ ⨆ _i : Unit,
        ringKrullDim ((⊤ : Subsemiring (ZMod 1)).comap (RingHom.id (ZMod 1))) := by
  constructor
  · exact ringKrullDim_eq_bot_of_subsingleton
  · exact ringKrullDim_subsemiring_le_iSup_comap_of_finite_subset_range
      (R := fun _ : Unit => ZMod 1) (fun _ => RingHom.id (ZMod 1)) ⊤
      (fun _ _ => ⟨(), fun x _ => ⟨x, rfl⟩⟩)

end FiniteCaptureTraceExamples
