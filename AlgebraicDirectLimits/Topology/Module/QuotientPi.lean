/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Quotient.Pi
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
public import Mathlib.Topology.Algebra.Module.Equiv

/-!
# Products of quotient topological modules

The canonical equivalence `Submodule.quotientPiL` identifies the quotient by a product
of submodules with the product of the coordinate quotients, for arbitrary dependent
families over a ring. Both sides have their original quotient and product topologies.
Only continuity of addition is needed; no separation or closedness is assumed.

The inverse is continuous because a product of the canonical open quotient maps is
again an open quotient map. No continuous choice of representatives is used.

## References

This extends Mathlib’s `Submodule.quotientPi` beyond finite products and commutative
rings, using `LinearMap.quotKerEquivOfSurjective` and
`IsOpenQuotientMap.piMap` for its algebraic and topological constructions.
-/

@[expose] public section

universe uR uI uM uN

namespace Submodule

variable {R : Type uR} [Ring R] {I : Type uI} {M : I → Type uM}
  [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
  [∀ i, TopologicalSpace (M i)] [∀ i, ContinuousAdd (M i)]

/-- The quotient by a product of submodules is continuously linearly equivalent to
the product of the coordinate quotients, with the original topologies. -/
noncomputable def quotientPiL (S : ∀ i, Submodule R (M i)) :
    ((∀ i, M i) ⧸ pi Set.univ S) ≃L[R] ∀ i, M i ⧸ S i := by
  let Q : (∀ i, M i) →L[R] ∀ i, M i ⧸ S i :=
    ContinuousLinearMap.piMap fun i => (S i).mkQL
  have hQ : IsOpenQuotientMap Q :=
    IsOpenQuotientMap.piMap fun i => (S i).isOpenQuotientMap_mkQL
  have hker : Q.ker = pi Set.univ S := by
    ext x
    change (fun i => (S i).mkQ (x i)) = 0 ↔ ∀ i ∈ Set.univ, x i ∈ S i
    simp only [funext_iff, Pi.zero_apply, mkQ_apply, Quotient.mk_eq_zero,
      Set.mem_univ, forall_const]
  let e := (quotEquivOfEq _ _ hker.symm).trans
    (Q.toLinearMap.quotKerEquivOfSurjective hQ.surjective)
  refine { toLinearEquiv := e, continuous_toFun := ?_, continuous_invFun := ?_ }
  · apply (isQuotientMap_mkQL (pi Set.univ S)).continuous_iff.mpr
    exact Q.continuous
  · apply hQ.isQuotientMap.continuous_iff.mpr
    have h : e.symm ∘ Q = (pi Set.univ S).mkQL := by
      funext x
      exact e.symm_apply_apply (Quotient.mk x)
    change Continuous (e.symm ∘ Q)
    rw [h]
    exact (pi Set.univ S).mkQL.continuous

/-- On a quotient representative, the equivalence takes each coordinate class. -/
@[simp]
theorem quotientPiL_mk (S : ∀ i, Submodule R (M i)) (x : ∀ i, M i) :
    quotientPiL S (Quotient.mk x) = fun i => Quotient.mk (x i) :=
  rfl

/-- The inverse sends a family of coordinate classes to the class of the family. -/
@[simp]
theorem quotientPiL_symm_mk (S : ∀ i, Submodule R (M i)) (x : ∀ i, M i) :
    (quotientPiL S).symm (fun i => Quotient.mk (x i)) = Quotient.mk x := by
  rw [← quotientPiL_mk S x, ContinuousLinearEquiv.symm_apply_apply]

/-- A coordinate of the equivalence is the quotient map induced by projection. -/
theorem quotientPiL_apply (S : ∀ i, Submodule R (M i))
    (x : (∀ i, M i) ⧸ pi Set.univ S) (i : I) :
    quotientPiL S x i =
      (pi Set.univ S).mapQ (S i) (LinearMap.proj i)
        (fun _ hx => mem_pi.mp hx i (Set.mem_univ i)) x := by
  induction x using Quotient.induction_on with
  | _ x => rfl

variable {N : I → Type uN} [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]
  [∀ i, TopologicalSpace (N i)] [∀ i, ContinuousAdd (N i)]

/-- The product-quotient equivalence commutes with compatible coordinate maps.
The containment for the product map follows from the coordinate containments. -/
theorem quotientPiL_naturality (S : ∀ i, Submodule R (M i))
    (T : ∀ i, Submodule R (N i)) (f : ∀ i, M i →L[R] N i)
    (h : ∀ i, S i ≤ (T i).comap (f i).toLinearMap)
    (x : (∀ i, M i) ⧸ pi Set.univ S) :
    quotientPiL T
        ((pi Set.univ S).mapQ (pi Set.univ T)
          (LinearMap.piMap fun i => (f i).toLinearMap)
          (fun _ hy => mem_pi.mpr fun i _ =>
            h i (mem_pi.mp hy i (Set.mem_univ i))) x) =
      fun i => (S i).mapQ (T i) (f i).toLinearMap (h i) (quotientPiL S x i) := by
  induction x using Quotient.induction_on with
  | _ x =>
    simp only [mapQ_apply, quotientPiL_mk]
    rfl

end Submodule

namespace Submodule

variable {R : Type uR} [CommRing R] {I : Type uI} [Fintype I] [DecidableEq I]
  {M : I → Type uM} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
  [∀ i, TopologicalSpace (M i)] [∀ i, ContinuousAdd (M i)]

/-- For finite products over a commutative ring, the underlying linear equivalence
is Mathlib’s `Submodule.quotientPi`. -/
theorem quotientPiL_toLinearEquiv (S : ∀ i, Submodule R (M i)) :
    (quotientPiL S).toLinearEquiv = quotientPi S := by
  apply LinearEquiv.ext
  intro x
  induction x using Quotient.induction_on with
  | _ x => rfl

end Submodule
