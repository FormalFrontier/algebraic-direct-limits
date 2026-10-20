/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicDirectLimits.Topology.TensorProduct
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Instances.ZMod
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Infinite free coefficients and compact right scalars

Over the two-element ring, the countable direct sum of copies of the ring is
free and projective but not finitely generated. The scalar right factor has its
canonical discrete topology and is nontrivial, compact and Hausdorff.

The algebraic right unitor identifies the one-sided tensor with a discrete
copy of the coefficient module. Its forward continuity uses the outgoing
linear generator criterion; inverse continuity uses the discrete target as
domain. The discrete copy retains exactly the coefficient module's action and
is not a topology input to the tensor construction. Basis tensors and a sum
with two different support coordinates exhibit nonzero and distinct values.

## References

The example reuses the one-sided tensor topology and linear generator criterion
of Algebraic Direct Limits, following Formal Frontier Agents, including
Beacon's topological development, and Richard Hill and Andrew Yang's Mathlib
coinduced topological-module construction. Module-category data are due to
Robert A. Spencer and Markus Himmel. The algebraic right unitor is due to
Kenny Lau and Mario Carneiro; the Finsupp basis and single-vector API to
Johannes Hölzl and Kim Morrison; freeness to Riccardo Brasca; projectivity to
Kevin Buzzard and Antoine Labelle; and finite-module cardinality to Johan
Commelin. The scalar ring API is due to Eric Rodriguez and Chris Hughes, with
the discrete topology by David Loeffler. Ring topology reuses Patrick Massot
and Johannes Hölzl's work; joint scalar continuity Yury Kudryashov's; and
topological monoids Johannes Hölzl, Mario Carneiro and Mitchell Lee's.
Continuous linear equivalences reuse Jan-David Salchow, Sébastien Gouëzel,
Jean Lo, Yury Kudryashov, Frédéric Dupuis and Heather Macbeth's work. Topology
ordering and separation reuse Johannes Hölzl and Mario Carneiro's work, and
compactness Johannes Hölzl, Mario Carneiro and Yury Kudryashov's.
-/

@[expose] public section

open scoped TensorProduct

namespace TensorNoncompactness

/-- The ring of two elements, with its canonical ring structure and discrete topology. -/
abbrev R : Type := ZMod 2

/-- The unit of the scalar ring is nonzero. -/
theorem R_one_ne_zero : (1 : R) ≠ 0 := by
  intro h
  exact (by decide : (2 : ℕ) ≠ 1) ((ZMod.one_eq_zero_iff (n := 2)).mp h)

/-- Zero and one are different scalar values. -/
theorem R_zero_ne_one : (0 : R) ≠ 1 := R_one_ne_zero.symm

/-- The scalar ring is nontrivial. -/
theorem R_nontrivial : Nontrivial R := by
  let : Fact (1 < (2 : ℕ)) := ⟨by decide⟩
  exact ZMod.nontrivial 2

/-- The scalar ring has two elements. -/
theorem R_card : Fintype.card R = 2 := ZMod.card 2

/-- Every scalar is either zero or one. -/
theorem R_eq_zero_or_one (r : R) : r = 0 ∨ r = 1 :=
  (by decide : ∀ r : R, r = 0 ∨ r = 1) r

/-- The scalar topology is the stock discrete topology. -/
theorem R_topologicalSpace : (inferInstance : TopologicalSpace R) = ⊥ := rfl

/-- The countable direct sum of copies of the scalar ring, with coordinatewise action. -/
noncomputable abbrev C : ModuleCat R := ModuleCat.of R (ℕ →₀ R)

/-- The coefficient carrier is the finitely supported function module. -/
@[simp]
theorem coe_C : (C : Type) = (ℕ →₀ R) := rfl

/-- The stored coefficient module is the canonical Finsupp module. -/
theorem C_isModule : C.isModule = (inferInstance : Module R (ℕ →₀ R)) := rfl

/-- Scalar multiplication on coefficients is coordinatewise multiplication. -/
@[simp]
theorem C_smul_apply (r : R) (c : C) (n : ℕ) : (r • c) n = r * c n := by
  simp only [Finsupp.smul_apply, smul_eq_mul]

/-- The coefficient with value one at one index and zero elsewhere. -/
noncomputable def basisVector (n : ℕ) : C := Finsupp.single n 1

/-- The coefficient basis vector is the single-one finitely supported coefficient. -/
theorem basisVector_eq_single (n : ℕ) :
    @Eq (ℕ →₀ R) (basisVector n) (Finsupp.single n (1 : R)) := by
  rfl

/-- A basis vector has exactly one nonzero coordinate. -/
@[simp]
theorem basisVector_apply (n k : ℕ) :
    basisVector n k = if n = k then 1 else 0 :=
  Finsupp.single_apply

/-- Each coefficient basis vector is nonzero. -/
theorem basisVector_ne_zero (n : ℕ) : basisVector n ≠ 0 :=
  Finsupp.single_ne_zero.mpr R_one_ne_zero

/-- Different natural-number indices give different coefficient vectors. -/
theorem basisVector_injective : Function.Injective basisVector :=
  Finsupp.single_left_injective R_one_ne_zero

/-- The canonical natural-number-indexed basis of the coefficient module. -/
noncomputable def coefficientBasis : Module.Basis ℕ R C := Finsupp.basisSingleOne

/-- The canonical basis consists of the single-coordinate vectors. -/
@[simp]
theorem coefficientBasis_apply (n : ℕ) : coefficientBasis n = basisVector n :=
  congrFun (Finsupp.coe_basisSingleOne (ι := ℕ) (R := R)) n

/-- Coordinates in the coefficient basis are the original finitely supported function. -/
@[simp]
theorem coefficientBasis_repr (c : C) : coefficientBasis.repr c = c := rfl

/-- The coefficient module is free, as witnessed by its canonical basis. -/
theorem C_moduleFree : Module.Free R C := Module.Free.of_basis coefficientBasis

/-- The coefficient module is projective because it is free. -/
theorem C_moduleProjective : Module.Projective R C := by
  let : Module.Free R C := C_moduleFree
  exact Module.Projective.of_free

/-- The coefficient module is not finitely generated. -/
theorem C_not_moduleFinite : ¬ Module.Finite R C := by
  let : Nontrivial R := R_nontrivial
  exact Module.not_finite_of_infinite_basis coefficientBasis

/-- The scalar right factor with the stock discrete topology and multiplication action. -/
abbrev M : TopModuleCat R := TopModuleCat.of R R

/-- The right-factor carrier is the scalar ring. -/
@[simp]
theorem coe_M : (M : Type) = R := rfl

/-- The right factor stores the canonical self-module. -/
theorem M_isModule : M.toModuleCat.isModule = (inferInstance : Module R R) := rfl

/-- The right factor uses the scalar ring's stock topology. -/
theorem M_topologicalSpace :
    M.topologicalSpace = (inferInstance : TopologicalSpace R) := rfl

/-- The right factor is discrete. -/
theorem M_discreteTopology : DiscreteTopology M := inferInstanceAs (DiscreteTopology R)

/-- The right factor has a finite carrier. -/
theorem M_finite : Finite M := inferInstanceAs (Finite R)

/-- The right factor has two elements. -/
theorem M_card : Fintype.card M = 2 := ZMod.card 2

/-- The right factor is nontrivial. -/
theorem M_nontrivial : Nontrivial M := R_nontrivial

/-- The right factor is compact because its carrier is finite. -/
theorem M_compactSpace : CompactSpace M := by
  let : Finite M := M_finite
  exact Finite.compactSpace

/-- The right factor is Hausdorff because it is discrete. -/
theorem M_t2Space : T2Space M := by
  let : DiscreteTopology M := M_discreteTopology
  exact DiscreteTopology.toT2Space

/-- Every right value is either zero or one. -/
theorem M_eq_zero_or_one (m : M) : m = 0 ∨ m = 1 := R_eq_zero_or_one m

/-- The unit right value is nonzero. -/
theorem M_one_ne_zero : (1 : M) ≠ 0 := R_one_ne_zero

/-- The stored self-action is ring multiplication. -/
@[simp]
theorem M_smul (r : R) (m : M) : r • m = r * m := smul_eq_mul r m

/-- Addition for the stored right-factor group is continuous. -/
theorem M_continuous_add : Continuous (fun p : M × M ↦ p.1 + p.2) := continuous_add

/-- Negation for the stored right-factor group is continuous. -/
theorem M_continuous_neg : Continuous (fun m : M ↦ -m) := continuous_neg

/-- Scalar multiplication for the stored right-factor module is jointly continuous. -/
theorem M_continuous_smul : Continuous (fun p : R × M ↦ p.1 • p.2) := continuous_smul

/-- A discrete target whose underlying algebraic module is exactly `C`. -/
noncomputable def D : TopModuleCat R := by
  letI : TopologicalSpace C := ⊥
  letI : DiscreteTopology C := discreteTopology_bot C
  letI : ContinuousAdd C := ⟨continuous_of_discreteTopology⟩
  letI : ContinuousNeg C := ⟨continuous_of_discreteTopology⟩
  letI : IsTopologicalAddGroup C := ⟨⟩
  letI : ContinuousSMul R C := ⟨continuous_of_discreteTopology⟩
  exact
    { toModuleCat := C
      topologicalSpace := inferInstance
      isTopologicalAddGroup := inferInstance
      continuousSMul := inferInstance }

/-- The target retains the coefficient module without changing its action. -/
@[simp]
theorem D_toModuleCat : D.toModuleCat = C := rfl

/-- The target carrier is the coefficient carrier. -/
@[simp]
theorem coe_D : (D : Type) = C := rfl

/-- The target stores the same module dictionary as the coefficients. -/
theorem D_isModule : D.toModuleCat.isModule = C.isModule := rfl

/-- The linear identification of the discrete target with finitely supported coefficients.

This uses Mathlib's linear-equivalence API by Nathaniel Thomas, Jeremy Avigad,
Johannes Hölzl, Mario Carneiro, Anne Baanen, Frédéric Dupuis and Heather Macbeth. -/
noncomputable def D_coefficientEquiv : D ≃ₗ[R] (ℕ →₀ R) :=
  LinearEquiv.cast (R := R) (M := fun X : ModuleCat R ↦ (X : Type)) D_toModuleCat

/-- The coefficient identification is the identity on finitely supported coefficients. -/
theorem D_coefficientEquiv_apply (c : ℕ →₀ R) : D_coefficientEquiv (c : D) = c := by
  unfold D_coefficientEquiv
  rfl

/-- The zero target value has zero finitely supported coefficients. -/
theorem D_zero_coefficient : D_coefficientEquiv (0 : D) = (0 : ℕ →₀ R) :=
  D_coefficientEquiv.map_zero

/-- Addition of target values adds their finitely supported coefficients. -/
theorem D_add_coefficient (d e : D) :
    D_coefficientEquiv (d + e) = D_coefficientEquiv d + D_coefficientEquiv e :=
  D_coefficientEquiv.map_add d e

/-- The target action acts coordinatewise on finitely supported coefficients. -/
theorem D_smul_coefficient (r : R) (d : D) :
    D_coefficientEquiv (r • d) = r • D_coefficientEquiv d :=
  D_coefficientEquiv.map_smul r d

/-- The coefficient identification sends the stored coefficient action to the finitely supported
coefficient action. -/
theorem D_coefficientEquiv_C_smul (r : R) (c : C) :
    @Eq (ℕ →₀ R)
      (D_coefficientEquiv
        (@SMul.smul R C C.isModule.toSMul r c : D))
      (r • D_coefficientEquiv (c : D)) := by
  change D_coefficientEquiv (r • (c : D)) = r • D_coefficientEquiv (c : D)
  exact D_smul_coefficient r (c : D)

/-- The target topology is discrete on the unchanged coefficient carrier. -/
theorem D_topologicalSpace : D.topologicalSpace = (⊥ : TopologicalSpace C) := rfl

/-- The bundled target is discrete. -/
theorem D_discreteTopology : DiscreteTopology D := ⟨D_topologicalSpace⟩

/-- The target retains coordinatewise scalar multiplication. -/
@[simp]
theorem D_smul_apply (r : R) (c : D) (n : ℕ) :
    D_coefficientEquiv (r • c) n = r * D_coefficientEquiv c n := by
  simp only [D_smul_coefficient, Finsupp.smul_apply, smul_eq_mul]

/-- Addition for the stored target group is continuous. -/
theorem D_continuous_add : Continuous (fun p : D × D ↦ p.1 + p.2) := continuous_add

/-- Negation for the stored target group is continuous. -/
theorem D_continuous_neg : Continuous (fun c : D ↦ -c) := continuous_neg

/-- Scalar multiplication for the stored target module is jointly continuous. -/
theorem D_continuous_smul : Continuous (fun p : R × D ↦ p.1 • p.2) := continuous_smul

/-- The one-sided tensor of the algebraic coefficients and the compact scalar right factor. -/
noncomputable abbrev T : TopModuleCat R := TopModuleCat.tensorLeftObj R C M

/-- The tensor carrier is the unchanged algebraic tensor product. -/
@[simp]
theorem coe_T : (T : Type) = TensorProduct R C M :=
  TopModuleCat.coe_tensorLeftObj R C M

/-- The tensor stores the canonical algebraic tensor module. -/
theorem T_isModule :
    T.toModuleCat.isModule = (inferInstance : Module R (TensorProduct R C M)) := rfl

/-- The algebraic right unitor as a continuous linear map into the discrete target. -/
noncomputable def rightUnitMap : T →L[R] D where
  toLinearMap := (TensorProduct.rid R C).toLinearMap
  cont := by
    let : DiscreteTopology M := M_discreteTopology
    apply (TopModuleCat.continuous_tensorLeftObj_iff_tmul R C M D
      (show T →ₗ[R] D from (TensorProduct.rid R C).toLinearMap)).mpr
    intro c
    exact continuous_of_discreteTopology

/-- Forgetting continuity gives the stock algebraic right unitor map. -/
@[simp]
theorem rightUnitMap_toLinearMap :
    rightUnitMap.toLinearMap = (TensorProduct.rid R C).toLinearMap := rfl

/-- The right unitor sends a pure tensor to its scalar multiple. -/
@[simp]
theorem rightUnitMap_tmul (c : C) (r : M) :
    rightUnitMap (c ⊗ₜ[R] r) = r • c := TensorProduct.rid_tmul c r

/-- The right unitor evaluates a fixed-coefficient generator by scalar multiplication. -/
@[simp]
theorem rightUnitMap_tensorGenerator (c : C) (r : M) :
    rightUnitMap (TopModuleCat.tensorGenerator R C M c r) = r • c := by
  rw [TopModuleCat.tensorGenerator_apply, rightUnitMap_tmul]

/-- The right unitor with both continuity directions for the discrete coefficient target. -/
noncomputable def rightUnit : T ≃L[R] D where
  toLinearEquiv := TensorProduct.rid R C
  continuous_toFun := rightUnitMap.continuous
  continuous_invFun := by
    let : DiscreteTopology D := D_discreteTopology
    exact continuous_of_discreteTopology

/-- The underlying linear equivalence is exactly the algebraic right unitor. -/
@[simp]
theorem rightUnit_toLinearEquiv :
    rightUnit.toLinearEquiv = TensorProduct.rid R C := rfl

/-- The continuous linear map of the equivalence is `rightUnitMap`. -/
@[simp]
theorem rightUnit_toContinuousLinearMap :
    rightUnit.toContinuousLinearMap = rightUnitMap := rfl

/-- The continuous right unitor has the same pure-tensor formula. -/
@[simp]
theorem rightUnit_tmul (c : C) (r : M) :
    rightUnit (c ⊗ₜ[R] r) = r • c := TensorProduct.rid_tmul c r

/-- The inverse right unitor tensors a coefficient with the unit right value. -/
@[simp]
theorem rightUnit_symm_apply (c : D) : rightUnit.symm c = c ⊗ₜ[R] (1 : M) :=
  TensorProduct.rid_symm_apply c

/-- The right unitor evaluates every continuous tensor generator by the stored action. -/
@[simp]
theorem rightUnit_tensorGenerator (c : C) (r : M) :
    rightUnit (TopModuleCat.tensorGenerator R C M c r) = r • c := by
  rw [TopModuleCat.tensorGenerator_apply, rightUnit_tmul]

/-- Forward followed by inverse is the identity on the tensor. -/
theorem rightUnit_symm_apply_apply (x : T) : rightUnit.symm (rightUnit x) = x :=
  rightUnit.symm_apply_apply x

/-- Inverse followed by forward is the identity on the target. -/
theorem rightUnit_apply_symm_apply (c : D) : rightUnit (rightUnit.symm c) = c :=
  rightUnit.apply_symm_apply c

/-- The homeomorphism obtained by forgetting linearity of the continuous right unitor. -/
noncomputable def rightUnitHomeomorph : T ≃ₜ D := rightUnit.toHomeomorph

/-- The homeomorphism has the same forward map as the continuous right unitor. -/
@[simp]
theorem rightUnitHomeomorph_apply (x : T) : rightUnitHomeomorph x = rightUnit x := rfl

/-- The inverse homeomorphism tensors with the unit right value. -/
@[simp]
theorem rightUnitHomeomorph_symm_apply (c : D) :
    rightUnitHomeomorph.symm c = c ⊗ₜ[R] (1 : M) := rightUnit_symm_apply c

/-- A coefficient basis vector tensored with the nonzero right unit. -/
noncomputable def tensorVector (n : ℕ) : T := basisVector n ⊗ₜ[R] (1 : M)

/-- A basis tensor is the generator at its coefficient evaluated at one. -/
theorem tensorVector_eq_tensorGenerator (n : ℕ) :
    tensorVector n = TopModuleCat.tensorGenerator R C M (basisVector n) (1 : M) := rfl

/-- The right unitor detects the coefficient basis vector of a basis tensor. -/
@[simp]
theorem rightUnitMap_tensorVector (n : ℕ) : rightUnitMap (tensorVector n) = basisVector n := by
  exact (rightUnitMap_tmul (basisVector n) 1).trans (one_smul R (basisVector n))

/-- Every basis tensor is nonzero. -/
theorem tensorVector_ne_zero (n : ℕ) : tensorVector n ≠ 0 := by
  intro h
  apply basisVector_ne_zero n
  have hcoeff := congrArg (fun x : T ↦ D_coefficientEquiv (rightUnitMap x)) h
  rw [map_zero rightUnitMap, D_zero_coefficient] at hcoeff
  simpa only [rightUnitMap_tensorVector, D_coefficientEquiv_apply] using hcoeff

/-- Distinct coefficient indices remain distinct in the tensor. -/
theorem tensorVector_injective : Function.Injective tensorVector := by
  intro i j h
  apply basisVector_injective
  simpa only [rightUnitMap_tensorVector, D_coefficientEquiv_apply] using
    congrArg (fun x : T ↦ D_coefficientEquiv (rightUnitMap x)) h

/-- The tensor is nontrivial, as witnessed by a basis tensor. -/
theorem T_nontrivial : Nontrivial T := ⟨⟨tensorVector 0, 0, tensorVector_ne_zero 0⟩⟩

/-- Coefficient variation gives distinct tensors at indices zero and one. -/
theorem tensorVector_zero_ne_one : tensorVector 0 ≠ tensorVector 1 := by
  intro h
  exact (by decide : (0 : ℕ) ≠ 1) (tensorVector_injective h)

/-- Adding two basis tensors retains both coefficient support coordinates. -/
theorem tensorVector_add_eq_tmul :
    tensorVector 0 + tensorVector 1 = (basisVector 0 + basisVector 1) ⊗ₜ[R] (1 : M) :=
  (TensorProduct.add_tmul (basisVector 0) (basisVector 1) (1 : M)).symm

/-- A tensor with two different support coordinates is nonzero. -/
theorem tensorVector_add_ne_zero : tensorVector 0 + tensorVector 1 ≠ 0 := by
  intro h
  have hcoord := congrArg (fun x : T ↦ D_coefficientEquiv (rightUnitMap x) 0) h
  rw [map_add rightUnitMap, map_zero rightUnitMap, D_add_coefficient,
    D_zero_coefficient] at hcoord
  have hone : (1 : R) = 0 := by
    simpa only [rightUnitMap_tensorVector, D_coefficientEquiv_apply, basisVector_eq_single,
      Finsupp.add_apply, Finsupp.zero_apply, Finsupp.single_apply, ite_true,
      ite_eq_right (by decide : (1 : ℕ) ≠ 0), add_zero] using hcoord
  exact R_one_ne_zero hone

/-- The two-coordinate tensor differs from its first summand. -/
theorem tensorVector_add_ne_left : tensorVector 0 + tensorVector 1 ≠ tensorVector 0 := by
  intro h
  have hcoord := congrArg (fun x : T ↦ D_coefficientEquiv (rightUnitMap x) 1) h
  rw [map_add rightUnitMap, D_add_coefficient] at hcoord
  have hone : (1 : R) = 0 := by
    simpa only [rightUnitMap_tensorVector, D_coefficientEquiv_apply, basisVector_eq_single,
      Finsupp.add_apply, Finsupp.single_apply, ite_true,
      ite_eq_right (by decide : (0 : ℕ) ≠ 1), zero_add] using hcoord
  exact R_one_ne_zero hone

/-- The two-coordinate tensor differs from its second summand. -/
theorem tensorVector_add_ne_right : tensorVector 0 + tensorVector 1 ≠ tensorVector 1 := by
  intro h
  have hcoord := congrArg (fun x : T ↦ D_coefficientEquiv (rightUnitMap x) 0) h
  rw [map_add rightUnitMap, D_add_coefficient] at hcoord
  have hone : (1 : R) = 0 := by
    simpa only [rightUnitMap_tensorVector, D_coefficientEquiv_apply, basisVector_eq_single,
      Finsupp.add_apply, Finsupp.single_apply, ite_true,
      ite_eq_right (by decide : (1 : ℕ) ≠ 0), add_zero] using hcoord
  exact R_one_ne_zero hone

/-- The zero right value gives the zero tensor for every coefficient. -/
@[simp]
theorem tmul_right_zero (c : C) : (c ⊗ₜ[R] (0 : M) : T) = 0 := TensorProduct.tmul_zero M c

/-- Right values zero and one give different tensors at a nonzero coefficient. -/
theorem tmul_zero_ne_tmul_one :
    (basisVector 0 ⊗ₜ[R] (0 : M) : T) ≠ basisVector 0 ⊗ₜ[R] (1 : M) := by
  rw [tmul_right_zero]
  exact (tensorVector_ne_zero 0).symm

/-- The right unitor respects scalar variation on each basis tensor. -/
@[simp]
theorem rightUnitMap_smul_tensorVector (r : R) (n : ℕ) :
    rightUnitMap (r • tensorVector n) = r • basisVector n := by
  apply D_coefficientEquiv.injective
  rw [map_smul rightUnitMap, D_smul_coefficient, rightUnitMap_tensorVector]
  exact (D_coefficientEquiv_C_smul r (basisVector n)).symm

/-- Zero and one scalars give different values on a nonzero tensor. -/
theorem zero_smul_ne_one_smul : (0 : R) • tensorVector 0 ≠ (1 : R) • tensorVector 0 := by
  simpa only [zero_smul, one_smul] using (tensorVector_ne_zero 0).symm

/-- Infinite free coefficients with compact scalar right input need not give a compact tensor. -/
theorem not_compactSpace_tensor : ¬ CompactSpace (TopModuleCat.tensorLeftObj R C M) := by
  intro h
  let : CompactSpace T := h
  let : CompactSpace D := rightUnitHomeomorph.compactSpace
  let : DiscreteTopology D := D_discreteTopology
  let : Finite D := finite_of_compact_of_discrete
  exact not_injective_infinite_finite (fun n ↦ rightUnitHomeomorph (tensorVector n))
    (rightUnitHomeomorph.injective.comp tensorVector_injective)

/-- The linear identification of the discrete target with finitely supported coefficients. -/
noncomputable abbrev dCoefficientEquiv : D ≃ₗ[R] (ℕ →₀ R) :=
  D_coefficientEquiv

-- The deprecated coefficient-equivalence identifier is retained for existing applications.
attribute [nolint defsWithUnderscore] D_coefficientEquiv
attribute [deprecated dCoefficientEquiv (since := "2026-10-20")] D_coefficientEquiv

end TensorNoncompactness
