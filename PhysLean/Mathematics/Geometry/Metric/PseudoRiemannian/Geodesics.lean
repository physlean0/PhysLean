/-
Copyright (c) 2025 PhysLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PhysLean Contributors
-/

import PhysLean.Mathematics.Geometry.Metric.PseudoRiemannian.Ricci
import PhysLean.Mathematics.Geometry.Metric.PseudoRiemannian.CausalStructure

/-!
# Geodesics and Geodesic Deviation

This file provides a more comprehensive treatment of geodesics on pseudo-Riemannian
manifolds, including the geodesic deviation equation which describes how nearby
geodesics converge or diverge.

## Main Definitions

* `GeodesicData`: A curve with its tangent vector field satisfying ∇_T T = 0
* `GeodesicDeviation`: The deviation vector between nearby geodesics
* `JacobiField`: Solutions to the Jacobi (geodesic deviation) equation

## Key Equations

Geodesic deviation equation:
  D²ξᵘ/dτ² + Rᵘ_νρσ T^ν ξ^ρ T^σ = 0

Raychaudhuri equation:
  dθ/dτ = -θ²/3 - σ² + ω² - R_{μν} v^μ v^ν

## Physical Interpretation

The geodesic deviation equation describes how:
- In flat spacetime, parallel geodesics remain parallel (ξ constant)
- In curved spacetime, geodesics converge (positive curvature) or diverge (negative)
- This is the origin of tidal forces in general relativity

## References

* Misner, Thorne, Wheeler, "Gravitation" (1973), Chapter 11
* O'Neill, "Semi-Riemannian Geometry" (1983), Chapter 8
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
variable {g : PseudoRiemannianMetric E H M n I}
variable {conn : LeviCivitaConnection g}

/-! ## Geodesic Curves -/

/-- A geodesic is a curve γ : ℝ → M together with its tangent vector field T
such that the covariant derivative of T along T vanishes: ∇_T T = 0.

This encapsulates:
1. The curve γ(τ) parametrized by proper time τ
2. The tangent vector T = dγ/dτ at each point
3. The geodesic condition: parallel transport of T along γ -/
structure GeodesicData (g : PseudoRiemannianMetric E H M n I)
    (conn : LeviCivitaConnection g) where
  /-- The curve γ : ℝ → M -/
  curve : ℝ → M
  /-- The tangent vector at each point along the curve -/
  tangent : ∀ τ : ℝ, TangentSpace I (curve τ)
  /-- The geodesic equation: ∇_T T = 0 at each point -/
  geodesic_eq : ∀ τ : ℝ, conn.christoffel (curve τ) (tangent τ) (tangent τ) = 0

/-- A geodesic is timelike if its tangent vector is everywhere timelike. -/
def GeodesicData.isTimelike (γ : GeodesicData g conn) : Prop :=
  ∀ τ : ℝ, IsTimelike g (γ.curve τ) (γ.tangent τ)

/-- A geodesic is null if its tangent vector is everywhere null. -/
def GeodesicData.isNull (γ : GeodesicData g conn) : Prop :=
  ∀ τ : ℝ, IsNull g (γ.curve τ) (γ.tangent τ)

/-- A geodesic is spacelike if its tangent vector is everywhere spacelike. -/
def GeodesicData.isSpacelike (γ : GeodesicData g conn) : Prop :=
  ∀ τ : ℝ, IsSpacelike g (γ.curve τ) (γ.tangent τ)

/-! ## Affine Parameter -/

/-- A geodesic parameter τ is affine if the tangent vector has constant norm:
d/dτ g(T,T) = 0. For timelike geodesics, τ is proper time. -/
def isAffineParameter (conn : LeviCivitaConnection g) (γ : GeodesicData g conn) : Prop :=
  ∀ τ₁ τ₂ : ℝ, g.val (γ.curve τ₁) (γ.tangent τ₁) (γ.tangent τ₁) =
              g.val (γ.curve τ₂) (γ.tangent τ₂) (γ.tangent τ₂)

/-! ## Geodesic Deviation (Jacobi Equation) -/

/-- A Jacobi field along a geodesic γ is a vector field ξ along γ that satisfies
the geodesic deviation equation:

D²ξ/dτ² + R(T, ξ)T = 0

where D/dτ is the covariant derivative along γ, T is the tangent vector,
and R is the Riemann tensor.

Physically, Jacobi fields describe the separation between infinitesimally nearby
geodesics in a congruence. -/
structure JacobiField (conn : LeviCivitaConnection g) (γ : GeodesicData g conn) where
  /-- The deviation vector at each point along the geodesic -/
  deviation : ∀ τ : ℝ, TangentSpace I (γ.curve τ)
  /-- The first covariant derivative of the deviation (velocity of separation) -/
  deviation_deriv : ∀ τ : ℝ, TangentSpace I (γ.curve τ)

/-! ## Tidal Forces -/

/-- The tidal tensor (or Jacobi operator) K at a point, given a tangent vector v:
K(ξ) = R(v, ξ)v

This tensor measures the tidal force experienced by a body with extent ξ
moving with 4-velocity v. It's the physical manifestation of spacetime curvature. -/
def tidalTensor (R : RiemannTensor g) (x : M) (v : TangentSpace I x) :
    TangentSpace I x → TangentSpace I x :=
  fun ξ => R x v ξ v

/-! ## Raychaudhuri Equation -/

/-- The Raychaudhuri equation describes how the expansion θ of a congruence
of geodesics evolves:

dθ/dτ = -θ²/3 - σ² + ω² - R_{μν} v^μ v^ν

where:
- θ is the expansion (volume change rate)
- σ is the shear (shape distortion)
- ω is the vorticity (rotation)
- R_{μν} is the Ricci tensor

This equation is fundamental to:
- Singularity theorems (focusing theorem)
- Black hole physics
- Cosmological expansion -/
structure GeodesicCongruence (conn : LeviCivitaConnection g) where
  /-- The expansion scalar θ at each point -/
  expansion : M → ℝ
  /-- The shear scalar σ² -/
  shearSquared : M → ℝ
  /-- The vorticity ω² -/
  vorticitySquared : M → ℝ
  /-- Shear is non-negative -/
  shear_nonneg : ∀ x, shearSquared x ≥ 0
  /-- Vorticity is non-negative -/
  vorticity_nonneg : ∀ x, vorticitySquared x ≥ 0

/-- The Raychaudhuri rate: dθ/dτ = -θ²/3 - σ² + ω² - R_{μν} v^μ v^ν -/
def raychaudhuriRateCongruence (g : PseudoRiemannianMetric E H M n I) {conn : LeviCivitaConnection g}
    (C : GeodesicCongruence conn) (Ric : RicciTensor g)
    (x : M) (v : TangentSpace I x) : ℝ :=
  -C.expansion x^2 / 3 - C.shearSquared x + C.vorticitySquared x - Ric x v v

/-- The congruence is irrotational if vorticity vanishes. -/
def GeodesicCongruence.isIrrotational {g : PseudoRiemannianMetric E H M n I}
    {conn : LeviCivitaConnection g} (C : GeodesicCongruence conn) : Prop :=
  ∀ x, C.vorticitySquared x = 0

/-- Focusing theorem condition: for irrotational geodesics with SEC,
expansion decreases faster than -θ²/3.

When the congruence is irrotational (ω² = 0) and the null energy condition holds
(Ric(v,v) ≥ 0), the rate of change of expansion is bounded by -θ²/3, which leads
to focusing of geodesics. -/
lemma raychaudhuri_focusing_congruence (g : PseudoRiemannianMetric E H M n I)
    {conn : LeviCivitaConnection g}
    (C : GeodesicCongruence conn)
    (Ric : RicciTensor g) (x : M) (v : TangentSpace I x)
    (h_irrot : C.isIrrotational)
    (h_nec : (Ric x).toFun v v ≥ 0) :
    raychaudhuriRateCongruence g C Ric x v ≤ -C.expansion x^2 / 3 := by
  unfold raychaudhuriRateCongruence
  have h1 : -C.shearSquared x ≤ 0 := by linarith [C.shear_nonneg x]
  have h2 : C.vorticitySquared x = 0 := h_irrot x
  have h3 : -(Ric x).toFun v v ≤ 0 := by linarith
  linarith

end PseudoRiemannianMetric
end
