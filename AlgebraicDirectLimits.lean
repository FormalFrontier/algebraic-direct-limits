/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicDirectLimits.CofinalSequence
public import AlgebraicDirectLimits.CofinalGroupCompletion
public import AlgebraicDirectLimits.GradedStabilization
public import AlgebraicDirectLimits.LocalizationPi
public import AlgebraicDirectLimits.Matrix.Idempotent
public import AlgebraicDirectLimits.MittagLeffler
public import AlgebraicDirectLimits.MonoidalGroupCompletion
public import AlgebraicDirectLimits.Order.DirectedSystem
public import AlgebraicDirectLimits.PrimeSpectrumFilteredColimits
public import AlgebraicDirectLimits.RingTheory.DirectLimit
public import AlgebraicDirectLimits.RingTheory.KrullDimension.FiniteCapture
public import AlgebraicDirectLimits.RingTheory.KrullDimension.DirectLimit
public import AlgebraicDirectLimits.RingTheory.KrullDimension.DirectedUnion
public import AlgebraicDirectLimits.SimpleRing
public import AlgebraicDirectLimits.Topology.CoefficientTensor
public import AlgebraicDirectLimits.Topology.Coinduced
public import AlgebraicDirectLimits.Topology.ModuleTopology
public import AlgebraicDirectLimits.Topology.Module.Quotient
public import AlgebraicDirectLimits.Topology.Module.QuotientPi
public import AlgebraicDirectLimits.Topology.StrongDual
public import AlgebraicDirectLimits.Topology.Restriction
public import AlgebraicDirectLimits.Topology.RestrictionKernels
public import AlgebraicDirectLimits.Topology.RestrictionCokernels
public import AlgebraicDirectLimits.Topology.DiscreteScalarExtension
public import AlgebraicDirectLimits.Topology.DualTensorHom
public import AlgebraicDirectLimits.Topology.TensorCompactness
public import AlgebraicDirectLimits.Topology.TensorProduct
public import AlgebraicDirectLimits.Topology.TensorProduct.Map
public import AlgebraicDirectLimits.Topology.TensorProduct.Prod
public import AlgebraicDirectLimits.Topology.TensorProduct.Quotient
public import AlgebraicDirectLimits.Topology.TensorDiscrete
public import AlgebraicDirectLimits.Topology.TensorHom
public import AlgebraicDirectLimits.Topology.TensorFunctor
public import AlgebraicDirectLimits.Topology.TensorBifunctor
public import AlgebraicDirectLimits.Topology.TensorUnit
public import AlgebraicDirectLimits.Topology.TensorAssociativity
public import AlgebraicDirectLimits.Topology.TensorSeparation
public import AlgebraicDirectLimits.VaryingScalar

/-!
# Algebraic direct limits

Public entry point for directed limits with varying scalars, finite idempotent
matrix descent, tensor products, cofinal sequences and group completions,
monoidal object classes, graded stabilization, constant identity ring-homomorphism
systems, Type-valued Mittag--Leffler systems, filtered colimits of simple
rings, spectra of filtered ring colimits, Krull dimension under finite-subset
capture, for directed colimits and for directed subsemiring unions,
localization of countable products, one-sided tensor topologies, same-topology
scalar restriction with additivity and kernel and cokernel preservation,
discrete coefficient-algebra scalar extension, continuous dual tensor contraction
into bounded-convergence Hom spaces and its finite-left continuous linear
equivalence, continuous tensor associativity, compactness
for finitely generated coefficients, statements for arbitrary-basis and projective
tensor Hausdorffness, and linear continuity
for coinduced topological modules, the module topology on finite-dimensional
strong duals without complete scalars, and additive tensor functors with fixed algebraic
coefficients. Tensor functoriality in both variables uses the same one-sided
topology, with standard curried, uncurried and flipped presentations. For
independently based finite coefficient modules, coefficientwise continuity on the
left and joint right evaluation give joint tensor-map continuity on all tensors.
Each module may be imported independently.
-/
