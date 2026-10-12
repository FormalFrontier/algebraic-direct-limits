/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicDirectLimits
public import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# Finite-capture clients of the aggregate import

The singleton family recovers the surjective dimension bound. Independent index,
target and source universes also allow the bottom-dimension boundary for trivial
sources. Polynomial variables and coefficients are arbitrary in the finite-generated
subsemiring bound; this inequality does not compute either dimension.
-/

@[expose] public section

universe u v w

namespace AlgebraicDirectLimits.Tests.FiniteCapture

example {R : Type u} {S : Type v} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (hf : Function.Surjective f) : ringKrullDim S ≤ ringKrullDim R := by
  simpa using ringKrullDim_le_iSup_of_finite_subset_range
    (A := fun _ : Unit => R) (fun _ => f)
    (fun E _ => ⟨(), fun x _ => hf x⟩)

example {I : Type u} {B : Type v} [CommSemiring B]
    {A : I → Type w} [∀ i, CommSemiring (A i)] [∀ i, Subsingleton (A i)]
    (φ : ∀ i, A i →+* B)
    (hfinite : ∀ (E : Set B), E.Finite → ∃ i, E ⊆ Set.range (φ i)) : Subsingleton B := by
  apply ringKrullDim_eq_bot_iff_subsingleton.mp
  apply le_bot_iff.mp
  calc
    ringKrullDim B ≤ ⨆ i, ringKrullDim (A i) :=
      ringKrullDim_le_iSup_of_finite_subset_range φ hfinite
    _ = ⊥ := by simp [ringKrullDim_eq_bot_of_subsingleton]

example (σ : Type u) (R : Type v) [CommSemiring R] :
    ringKrullDim (MvPolynomial σ R) ≤
      ⨆ s : Finset (MvPolynomial σ R),
        ringKrullDim (Subsemiring.closure (s : Set (MvPolynomial σ R))) :=
  ringKrullDim_le_iSup_closure_finset _

end AlgebraicDirectLimits.Tests.FiniteCapture
