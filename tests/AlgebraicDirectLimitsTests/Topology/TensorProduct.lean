/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicDirectLimits.Topology.TensorProduct

/-!
# One-sided tensor type contracts

These contracts specify linear continuity, tensor maps, finite-basis coordinates,
basis change, coordinate naturality and separate compactness and Hausdorff
properties. They check types in the public tensor API's mathematical contexts;
they do not prove the specified propositions or construct their realizations.
-/

public section

open CategoryTheory

open scoped TensorProduct

universe uR uC uD uE uM uN uP uι uκ uI

namespace TopModuleCat

section Coinduced

variable {S : Type uR} [Ring S] [TopologicalSpace S]

variable {A : ModuleCat.{uC} S} {I : Type uI} {X : I → TopModuleCat.{uC} S}

#check (∀ (j : ∀ i, (X i).toModuleCat ⟶ A) (Y : TopModuleCat.{uN} S)
    (f : coinduced j →ₗ[S] Y),
    Continuous f ↔ ∀ i, Continuous (fun x : X i ↦ f (j i x)))

end Coinduced

variable (R : Type uR) [CommRing R] [TopologicalSpace R]

#check (∀ (C : ModuleCat.{uC} R) (M : TopModuleCat.{uM} R),
    (tensorLeftObj R C M).topologicalSpace =
      sInf {t : TopologicalSpace (TensorProduct R C M) |
        @ContinuousSMul R (TensorProduct R C M) _ _ t ∧
        @ContinuousAdd (TensorProduct R C M) t _ ∧
        ∀ c : C, M.topologicalSpace.coinduced ((TensorProduct.mk R C M) c) ≤ t})

#check (∀ (C : ModuleCat.{uC} R) (M : TopModuleCat.{uM} R) (N : TopModuleCat.{uN} R)
    (f : tensorLeftObj R C M →ₗ[R] N),
    Continuous f ↔ ∀ c : C, Continuous (fun m : M ↦ f (c ⊗ₜ[R] m)))

section TensorMaps

variable {C : ModuleCat.{uC} R} {D : ModuleCat.{uD} R} {E : ModuleCat.{uE} R}

variable {M : TopModuleCat.{uM} R} {N : TopModuleCat.{uN} R} {P : TopModuleCat.{uP} R}

#check (∀ (f : C →ₗ[R] D) (g : M →L[R] N),
    ∃ t : tensorLeftObj R C M →L[R] tensorLeftObj R D N,
      t.toLinearMap = TensorProduct.map f g.toLinearMap)

#check (∀ (f : C →ₗ[R] D) (g : M →L[R] N)
    (t : tensorLeftObj R C M →L[R] tensorLeftObj R D N),
    t.toLinearMap = TensorProduct.map f g.toLinearMap →
      ∀ c m, t (c ⊗ₜ[R] m) = f c ⊗ₜ[R] g m)

#check (∀ (t : tensorLeftObj R C M →L[R] tensorLeftObj R C M),
    t.toLinearMap = TensorProduct.map (LinearMap.id : C →ₗ[R] C)
      (LinearMap.id : M →ₗ[R] M) → t = ContinuousLinearMap.id R (tensorLeftObj R C M))

#check (∀ (f : C →ₗ[R] D) (f' : D →ₗ[R] E) (g : M →L[R] N) (g' : N →L[R] P)
    (t : tensorLeftObj R C M →L[R] tensorLeftObj R D N)
    (t' : tensorLeftObj R D N →L[R] tensorLeftObj R E P)
    (t'' : tensorLeftObj R C M →L[R] tensorLeftObj R E P),
    t.toLinearMap = TensorProduct.map f g.toLinearMap →
    t'.toLinearMap = TensorProduct.map f' g'.toLinearMap →
    t''.toLinearMap = TensorProduct.map (f'.comp f) (g'.comp g).toLinearMap →
      t'' = t'.comp t)

end TensorMaps

section Coordinates

variable (C : ModuleCat.{uC} R) (M : TopModuleCat.{uM} R)

variable {ι : Type uι} [Finite ι]

#check (∀ b : Module.Basis ι R C,
    ∃ e : tensorLeftObj R C M ≃L[R] (ι → M),
      e.toLinearEquiv = tensorCoordinateLinearEquiv R C M b)

#check (∀ (b : Module.Basis ι R C) (e : tensorLeftObj R C M ≃L[R] (ι → M)),
    e.toLinearEquiv = tensorCoordinateLinearEquiv R C M b →
      ∀ c m i, e (c ⊗ₜ[R] m) i = b.repr c i • m)

section FiniteSums

variable [Fintype ι]

#check (∀ (b : Module.Basis ι R C) (e : tensorLeftObj R C M ≃L[R] (ι → M)),
    e.toLinearEquiv = tensorCoordinateLinearEquiv R C M b →
      ∀ x : ι → M, e.symm x = ∑ i, b i ⊗ₜ[R] x i)

end FiniteSums

#check (∀ b : Module.Basis ι R C,
    (tensorLeftObj R C M).topologicalSpace =
      TopologicalSpace.induced (tensorCoordinateLinearEquiv R C M b) Pi.topologicalSpace)

#check (∀ (_b : Module.Basis ι R C), CompactSpace M → CompactSpace (tensorLeftObj R C M))

#check (∀ (_b : Module.Basis ι R C), T2Space M → T2Space (tensorLeftObj R C M))

end Coordinates

section BasisChange

variable (C : ModuleCat.{uC} R) (M : TopModuleCat.{uM} R)

variable {ι : Type uι} {κ : Type uκ} [Finite ι] [Finite κ]

#check (∀ (b : Module.Basis ι R C) (b' : Module.Basis κ R C),
    ∃ e : (ι → M) ≃L[R] (κ → M),
      e.toLinearEquiv = (tensorCoordinateLinearEquiv R C M b).symm.trans
        (tensorCoordinateLinearEquiv R C M b'))

section FiniteSums

variable [Fintype ι]

#check (∀ (b : Module.Basis ι R C) (b' : Module.Basis κ R C)
    (e : (ι → M) ≃L[R] (κ → M)),
    e.toLinearEquiv = (tensorCoordinateLinearEquiv R C M b).symm.trans
      (tensorCoordinateLinearEquiv R C M b') →
      ∀ (x : ι → M) (k : κ), e x k = ∑ i, b'.repr (b i) k • x i)

end FiniteSums

#check (∀ (b : Module.Basis ι R C) (b' : Module.Basis κ R C)
    (e : (ι → M) ≃L[R] (κ → M)) (e' : (κ → M) ≃L[R] (ι → M)),
    e.toLinearEquiv = (tensorCoordinateLinearEquiv R C M b).symm.trans
      (tensorCoordinateLinearEquiv R C M b') →
    e'.toLinearEquiv = (tensorCoordinateLinearEquiv R C M b').symm.trans
      (tensorCoordinateLinearEquiv R C M b) → e.symm = e')

end BasisChange

#check (∀ (C : ModuleCat.{uC} R) (M : TopModuleCat.{uM} R) (N : TopModuleCat.{uN} R)
    (ι : Type uι) [Finite ι] (b : Module.Basis ι R C) (g : M →L[R] N)
    (t : tensorLeftObj R C M →L[R] tensorLeftObj R C N),
    t.toLinearMap = TensorProduct.map (LinearMap.id : C →ₗ[R] C) g.toLinearMap →
      ∀ (x : tensorLeftObj R C M) (i : ι),
        tensorCoordinateLinearEquiv R C N b (t x) i =
          g (tensorCoordinateLinearEquiv R C M b x i))

#check (∀ (C : ModuleCat.{uC} R) (M : TopModuleCat.{uM} R)
    [Module.Free R C] [Module.Finite R C],
    CompactSpace M → CompactSpace (tensorLeftObj R C M))

#check (∀ (C : ModuleCat.{uC} R) (M : TopModuleCat.{uM} R)
    [Module.Free R C] [Module.Finite R C],
    T2Space M → T2Space (tensorLeftObj R C M))

#check (∀ (C : ModuleCat.{uC} R) (M : TopModuleCat.{uM} R)
    [Module.Free R C] [Module.Finite R C],
    ∃ e : tensorLeftObj R C M ≃L[R] (Module.Free.ChooseBasisIndex R C → M),
      e.toLinearEquiv = tensorCoordinateLinearEquiv R C M (Module.Free.chooseBasis R C))

end TopModuleCat
