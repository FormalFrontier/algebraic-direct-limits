/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicDirectLimits.CofinalSequence
public import AlgebraicDirectLimits.CofinalGroupCompletion
public import AlgebraicDirectLimits.GradedStabilization
public import AlgebraicDirectLimits.LocalizationPi
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
public import AlgebraicDirectLimits.Topology.Restriction
public import AlgebraicDirectLimits.Topology.DiscreteScalarExtension
public import AlgebraicDirectLimits.Topology.TensorCompactness
public import AlgebraicDirectLimits.Topology.TensorProduct
public import AlgebraicDirectLimits.Topology.TensorProduct.Prod
public import AlgebraicDirectLimits.Topology.TensorDiscrete
public import AlgebraicDirectLimits.Topology.TensorHom
public import AlgebraicDirectLimits.Topology.TensorUnit
public import AlgebraicDirectLimits.Topology.TensorAssociativity
public import AlgebraicDirectLimits.Topology.TensorSeparation
public import AlgebraicDirectLimits.VaryingScalar

/-!
# Algebraic direct limits

Public entry point for directed limits with varying scalars, tensor products,
cofinal sequences and group completions, monoidal object classes, graded
stabilization, constant identity ring-homomorphism systems, Type-valued
Mittag--Leffler systems, filtered colimits of simple
rings, spectra of filtered ring colimits, Krull dimension under finite-subset
capture, for directed colimits and for directed subsemiring unions,
localization of countable products, one-sided tensor topologies, same-topology
scalar restriction, discrete coefficient-algebra scalar extension, continuous
tensor associativity, compactness for finitely generated coefficients, statements
for arbitrary-basis and projective tensor Hausdorffness, and linear continuity
for coinduced topological modules.
Each module may be imported independently.
-/
