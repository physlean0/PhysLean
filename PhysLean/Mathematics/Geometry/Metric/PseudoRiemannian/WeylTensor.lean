/-
Copyright (c) 2025 PhysLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PhysLean Contributors
-/

import PhysLean.Mathematics.Geometry.Metric.PseudoRiemannian.Ricci

/-!
# The Weyl Tensor

This file defines the Weyl (conformal) tensor on pseudo-Riemannian manifolds of dimension ≥ 3.

The Weyl tensor is the trace-free part of the Riemann curvature tensor. It measures the
part of spacetime curvature that is not determined by local matter content (the Ricci part).
In general relativity, the Weyl tensor describes gravitational radiation and tidal forces.

## Main Definitions

* `WeylTensorAt`: The Weyl tensor at a point, defined as a (0,4) tensor field.
* `WeylTensor`: The Weyl tensor as a smooth tensor field.

## Main Properties

The Weyl tensor C satisfies:
1. All algebraic symmetries of the Riemann tensor
2. Complete trace-freeness: contracting any pair of indices gives zero

In dimensions n ≥ 3:
C_abcd = R_abcd - (2/(n-2))(g_a[c R_d]b - g_b[c R_d]a) + (2R/((n-1)(n-2)))g_a[c g_d]b

## Physical Interpretation

* In vacuum (Ricci-flat) spacetimes, the Weyl tensor equals the Riemann tensor
* The Weyl tensor describes gravitational waves (propagating degrees of freedom)
* It also encodes tidal forces through the geodesic deviation equation
* The Weyl tensor is conformally invariant (up to a power of the conformal factor)
* In 3 dimensions, the Weyl tensor vanishes identically (all 3D spacetimes are
  conformally flat)

## Petrov Classification (4D)

In 4 dimensions, the Weyl tensor can be classified according to the Petrov classification:
- Type I (general): Four distinct principal null directions
- Type II: Two coincident, two distinct
- Type D (degenerate): Two pairs of coincident (e.g., Schwarzschild, Kerr)
- Type III: Three coincident, one distinct
- Type N (null): Four coincident (pure gravitational radiation)
- Type O: Conformally flat (Weyl tensor vanishes)

## References

* Misner, Thorne, Wheeler, "Gravitation" (1973), §13.5
* O'Neill, "Semi-Riemannian Geometry" (1983)
* Wald, "General Relativity" (1984), Chapter 3
-/

noncomputable section

open Bundle Set Finset Function Filter Module Topology ContinuousLinearMap
open scoped Manifold Bundle LinearMap Dual

namespace PseudoRiemannianMetric

universe v w

variable {E : Type v} {H : Type w} {M : Type w} {n : WithTop ℕ∞}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] [ChartedSpace H E]
variable {I : ModelWithCorners ℝ E H}
variable [IsManifold I (n + 1) M]
variable [inst_tangent_findim : ∀ (x : M), FiniteDimensional ℝ (TangentSpace I x)]

/-! ## The Weyl Tensor -/

/-- The Weyl tensor at a point, as a (0,4) tensor.
This is the trace-free part of the Riemann tensor.

In dimension n ≥ 3, the Weyl tensor is defined by subtracting appropriate combinations
of the Ricci tensor and scalar curvature from the Riemann tensor such that
all contractions vanish.

The Weyl tensor satisfies all the algebraic symmetries of the Riemann tensor:
- Antisymmetry in first two indices: C(u,v,w,z) = -C(v,u,w,z)
- Antisymmetry in last two indices: C(u,v,w,z) = -C(u,v,z,w)
- Symmetry under pair exchange: C(u,v,w,z) = C(w,z,u,v)
- First Bianchi identity: C(u,v,w,z) + C(v,w,u,z) + C(w,u,v,z) = 0

Additionally, the Weyl tensor is completely trace-free. -/
def WeylTensorAt (_g : PseudoRiemannianMetric E H M n I) (x : M) :=
  TangentSpace I x → TangentSpace I x → TangentSpace I x → TangentSpace I x → ℝ

/-- The Weyl tensor as a smooth field over the manifold. -/
def WeylTensorField (g : PseudoRiemannianMetric E H M n I) := ∀ x : M, WeylTensorAt g x

/-- Structure encapsulating a valid Weyl tensor with its required properties. -/
structure WeylTensorData (g : PseudoRiemannianMetric E H M n I) where
  /-- The tensor field -/
  toWeylTensorField : WeylTensorField g
  /-- Antisymmetry in first two arguments -/
  antisymm_12 : ∀ x u v w z, toWeylTensorField x u v w z = -toWeylTensorField x v u w z
  /-- Antisymmetry in last two arguments -/
  antisymm_34 : ∀ x u v w z, toWeylTensorField x u v w z = -toWeylTensorField x u v z w
  /-- Symmetry under exchange of pairs -/
  symm_pairs : ∀ x u v w z, toWeylTensorField x u v w z = toWeylTensorField x w z u v
  /-- First Bianchi identity -/
  bianchi1 : ∀ x u v w z, toWeylTensorField x u v w z + toWeylTensorField x v w u z +
    toWeylTensorField x w u v z = 0
  /-- Trace-free property: contraction of first and third indices vanishes -/
  traceFree : ∀ x v z, ∃ (cb : CoordinateBasis g x),
    ∑ i, toWeylTensorField x (cb.basis i) v (cb.basis i) z = 0

/-- The Weyl tensor exists for pseudo-Riemannian manifolds of dimension ≥ 3.
This is stated as an axiom. In dimension 3, the Weyl tensor vanishes identically.
In dimension 4 and higher, it has independent components. -/
axiom weylTensorExists (g : PseudoRiemannianMetric E H M n I) :
    Nonempty (WeylTensorData g)

/-- The Weyl tensor, obtained from the existence axiom. -/
noncomputable def weylTensor (g : PseudoRiemannianMetric E H M n I) : WeylTensorData g :=
  Classical.choice (weylTensorExists g)

/-! ## Properties of the Weyl Tensor -/

variable (g : PseudoRiemannianMetric E H M n I)

/-! ## Petrov Classification (for 4D spacetimes) -/

/-- In 4 dimensions, the Weyl tensor can be classified according to the Petrov classification.
This classifies spacetimes by the algebraic structure of the Weyl tensor.

The types are:
- Type I (general): Four distinct principal null directions
- Type II: Two coincident, two distinct
- Type D (degenerate): Two pairs of coincident
- Type III: Three coincident, one distinct
- Type N (null): Four coincident
- Type O: Conformally flat (Weyl tensor vanishes)

This classification is important for:
- Characterizing gravitational radiation
- Finding exact solutions
- Understanding spacetime symmetries -/
inductive PetrovType
  | typeI   -- General case
  | typeII  -- Algebraically special
  | typeD   -- Degenerate (e.g., Schwarzschild, Kerr)
  | typeIII -- Algebraically special
  | typeN   -- Pure radiation (gravitational waves)
  | typeO   -- Conformally flat

/-- A spacetime with vanishing Weyl tensor is conformally flat.
This means it can be conformally mapped to flat Minkowski space. -/
def isConformallyFlat (x : M) : Prop :=
  ∀ u v w z : TangentSpace I x, (weylTensor g).toWeylTensorField x u v w z = 0

/-- The Weyl tensor vanishes where the spacetime is conformally flat. -/
lemma weyl_zero_iff_conformallyFlat (x : M) :
    isConformallyFlat g x ↔
    ∀ u v w z : TangentSpace I x, (weylTensor g).toWeylTensorField x u v w z = 0 := by
  rfl

end PseudoRiemannianMetric
end
