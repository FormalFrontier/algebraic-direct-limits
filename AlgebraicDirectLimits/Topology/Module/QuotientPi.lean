/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicDirectLimits.Topology.Module.Quotient

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

`Submodule.quotientProdL` gives the binary equivalence for two modules in independent
universes, without replacing their carriers or topologies. It commutes with compatible
semilinear maps through `ContinuousLinearMap.prodMapₛₗ`.

The inverse is continuous because a product of the canonical open quotient maps is
again an open quotient map. No continuous choice of representatives is used.

## References

This extends Mathlib’s `Submodule.quotientPi` beyond finite products and commutative
rings, using `LinearMap.quotKerEquivOfIsQuotientMap` and
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
  let e : ((∀ i, M i) ⧸ pi Set.univ S) ≃L[R] (∀ i, M i) ⧸ Q.ker :=
    { toLinearEquiv := quotEquivOfEq _ _ hker.symm
      continuous_toFun := by
        apply (pi Set.univ S).isQuotientMap_mkQ.continuous_iff.mpr
        exact Q.ker.mkQL.continuous
      continuous_invFun := by
        apply Q.ker.isQuotientMap_mkQ.continuous_iff.mpr
        exact (pi Set.univ S).mkQL.continuous }
  exact e.trans (Q.toLinearMap.quotKerEquivOfIsQuotientMap hQ.isQuotientMap)

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

universe uS uM₂ uN₂

namespace ContinuousLinearMap

section

variable {R : Type uR} {S : Type uS} [Semiring R] [Semiring S]
  {M : Type uM} {N : Type uN} {M₂ : Type uM₂} {N₂ : Type uN₂}
  [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid M₂] [AddCommMonoid N₂]
  [Module R M] [Module R N] [Module S M₂] [Module S N₂]
  [TopologicalSpace M] [TopologicalSpace N]
  [TopologicalSpace M₂] [TopologicalSpace N₂] {σ : R →+* S}

/-- The coordinatewise product of two continuous semilinear maps. -/
def prodMapₛₗ (f : M →SL[σ] M₂) (g : N →SL[σ] N₂) :
    M × N →SL[σ] M₂ × N₂ where
  toFun x := (f x.1, g x.2)
  map_add' x y := congrArg₂ Prod.mk (map_add f x.1 y.1) (map_add g x.2 y.2)
  map_smul' c x :=
    congrArg₂ Prod.mk (map_smulₛₗ f c x.1) (map_smulₛₗ g c x.2)
  cont := (f.continuous.comp continuous_fst).prodMk (g.continuous.comp continuous_snd)

/-- The semilinear product map acts coordinatewise. -/
@[simp]
theorem prodMapₛₗ_apply (f : M →SL[σ] M₂) (g : N →SL[σ] N₂) (x : M × N) :
    f.prodMapₛₗ g x = (f x.1, g x.2) := rfl

/-- The function underlying the semilinear product map is `Prod.map`. -/
@[simp, norm_cast]
theorem coe_prodMapₛₗ (f : M →SL[σ] M₂) (g : N →SL[σ] N₂) :
    ⇑(f.prodMapₛₗ g) = Prod.map f g := rfl

end

section

variable {R : Type uR} [Semiring R]
  {M : Type uM} {N : Type uN} {M₂ : Type uM₂} {N₂ : Type uN₂}
  [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid M₂] [AddCommMonoid N₂]
  [Module R M] [Module R N] [Module R M₂] [Module R N₂]
  [TopologicalSpace M] [TopologicalSpace N]
  [TopologicalSpace M₂] [TopologicalSpace N₂]

/-- At the identity ring homomorphism, the semilinear product is `prodMap`. -/
@[simp]
theorem prodMapₛₗ_id (f : M →L[R] M₂) (g : N →L[R] N₂) :
    f.prodMapₛₗ g = f.prodMap g := by
  ext x <;> rfl

end

end ContinuousLinearMap

namespace Submodule

variable {R : Type uR} [Ring R] {M : Type uM} {N : Type uN}
  [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
  [TopologicalSpace M] [TopologicalSpace N]
  [ContinuousAdd M] [ContinuousAdd N]

/-- The quotient by a product of submodules is continuously linearly equivalent to
the product of the two quotients, with their original topologies. -/
noncomputable def quotientProdL (P : Submodule R M) (Q : Submodule R N) :
    ((M × N) ⧸ P.prod Q) ≃L[R] (M ⧸ P) × (N ⧸ Q) := by
  let F : M × N →L[R] (M ⧸ P) × (N ⧸ Q) := P.mkQL.prodMap Q.mkQL
  have hF : IsOpenQuotientMap F :=
    P.isOpenQuotientMap_mkQL.prodMap Q.isOpenQuotientMap_mkQL
  have hker : F.ker = P.prod Q :=
    (LinearMap.ker_prodMap P.mkQ Q.mkQ).trans
      (congrArg₂ (fun (A : Submodule R M) (B : Submodule R N) => A.prod B)
        (ker_mkQ P) (ker_mkQ Q))
  let e : ((M × N) ⧸ P.prod Q) ≃L[R] (M × N) ⧸ F.ker :=
    { toLinearEquiv := quotEquivOfEq _ _ hker.symm
      continuous_toFun := by
        apply (P.prod Q).isQuotientMap_mkQ.continuous_iff.mpr
        exact F.ker.mkQL.continuous
      continuous_invFun := by
        apply F.ker.isQuotientMap_mkQ.continuous_iff.mpr
        exact (P.prod Q).mkQL.continuous }
  exact e.trans (F.toLinearMap.quotKerEquivOfIsQuotientMap hF.isQuotientMap)

variable (P : Submodule R M) (Q : Submodule R N)

/-- A pair representative maps to the pair of its coordinate classes. -/
@[simp]
theorem quotientProdL_mk (m : M) (n : N) :
    quotientProdL P Q (Quotient.mk (m, n)) = (Quotient.mk m, Quotient.mk n) := rfl

/-- The inverse sends a pair of representative classes to the class of the pair. -/
@[simp]
theorem quotientProdL_symm_mk (m : M) (n : N) :
    (quotientProdL P Q).symm (Quotient.mk m, Quotient.mk n) = Quotient.mk (m, n) := by
  rw [← quotientProdL_mk P Q m n, ContinuousLinearEquiv.symm_apply_apply]

/-- The product-quotient equivalence commutes with the canonical quotient maps. -/
theorem quotientProdL_mkQL :
    (quotientProdL P Q).toContinuousLinearMap.comp (P.prod Q).mkQL =
      P.mkQL.prodMap Q.mkQL := by
  apply ContinuousLinearMap.ext
  intro x
  exact quotientProdL_mk P Q x.1 x.2

/-- The underlying linear map is the canonical quotient lift of the product map. -/
theorem quotientProdL_toLinearMap :
    (quotientProdL P Q).toLinearEquiv.toLinearMap =
      (P.prod Q).liftQ (P.mkQ.prodMap Q.mkQ)
        (((LinearMap.ker_prodMap P.mkQ Q.mkQ).trans
          (congrArg₂ (fun (A : Submodule R M) (B : Submodule R N) => A.prod B)
            (ker_mkQ P) (ker_mkQ Q))).ge) := by
  apply LinearMap.ext
  intro x
  induction x using Quotient.induction_on with
  | _ x => exact quotientProdL_mk P Q x.1 x.2

/-- Values on pair representatives uniquely determine the continuous linear map. -/
theorem quotientProdL_unique
    (g : ((M × N) ⧸ P.prod Q) →L[R] (M ⧸ P) × (N ⧸ Q))
    (hg : ∀ m n, g (Quotient.mk (m, n)) = (Quotient.mk m, Quotient.mk n)) :
    g = (quotientProdL P Q).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro x
  induction x using Quotient.induction_on with
  | _ x => exact (hg x.1 x.2).trans (quotientProdL_mk P Q x.1 x.2).symm

variable {S : Type uS} [Ring S] {M₂ : Type uM₂} {N₂ : Type uN₂}
  [AddCommGroup M₂] [AddCommGroup N₂] [Module S M₂] [Module S N₂]
  [TopologicalSpace M₂] [TopologicalSpace N₂]
  [ContinuousAdd M₂] [ContinuousAdd N₂] {σ : R →+* S}

/-- The binary product-quotient equivalence commutes with compatible semilinear maps.
The product containment follows from the two coordinate containments. -/
theorem quotientProdL_naturality
    (P₂ : Submodule S M₂) (Q₂ : Submodule S N₂)
    (f : M →SL[σ] M₂) (g : N →SL[σ] N₂)
    (hf : P ≤ P₂.comap f.toLinearMap) (hg : Q ≤ Q₂.comap g.toLinearMap)
    (x : (M × N) ⧸ P.prod Q) :
    quotientProdL P₂ Q₂
        ((P.prod Q).mapQL (P₂.prod Q₂) (f.prodMapₛₗ g)
          (fun _z hz => ⟨hf hz.1, hg hz.2⟩) x) =
      ((P.mapQL P₂ f hf) (quotientProdL P Q x).1,
       (Q.mapQL Q₂ g hg) (quotientProdL P Q x).2) := by
  induction x using Quotient.induction_on with
  | _ x =>
    rcases x with ⟨m, n⟩
    rw [quotientProdL_mk P Q m n]
    exact quotientProdL_mk P₂ Q₂ (f m) (g n)

end Submodule
