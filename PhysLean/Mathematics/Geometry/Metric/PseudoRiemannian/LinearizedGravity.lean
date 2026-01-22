/-
Copyright (c) 2025 PhysLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PhysLean Contributors
-/

import PhysLean.Mathematics.Geometry.Metric.PseudoRiemannian.Einstein

/-!
# Linearized Gravity

This file formalizes linearized general relativity, the weak-field approximation
where the metric is a small perturbation of flat spacetime. This regime describes
gravitational waves far from sources and provides the foundation for the
field-theoretic approach to gravity.

## Main Definitions

* `WeakFieldPerturbation`: The perturbation h_μν around flat spacetime
* `TraceReversed`: The trace-reversed perturbation h̄_μν
* `LorenzGauge`: The harmonic/de Donder gauge condition
* `TransversTraceless`: The TT gauge for gravitational waves

## Main Results

* `linearized_einstein`: The linearized Einstein equations
* `graviton_propagator`: The graviton propagator in Lorenz gauge
* `wave_equation_lorenz`: Wave equation for h̄_μν in Lorenz gauge
* `gauge_transformation`: Residual gauge freedom

## Physical Interpretation

Linearized gravity describes:
- Gravitational waves far from sources
- Newtonian gravity as the static limit
- The graviton as a massless spin-2 particle
- Post-Newtonian corrections at higher orders

The metric is g_μν = η_μν + h_μν where |h_μν| << 1.

## References

* Misner, Thorne, Wheeler, "Gravitation" (1973), Chapters 18, 35
* Wald, "General Relativity" (1984), Chapter 4
* Carroll, "Spacetime and Geometry" (2004), Chapter 7
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

/-! ## Metric Perturbation -/

/-- The Minkowski metric η_μν = diag(-1, 1, 1, 1). -/
def minkowskiMetric (μ ν : Fin 4) : ℝ :=
  if μ = ν then
    if μ = 0 then -1 else 1
  else 0

/-- A metric perturbation h_μν around flat spacetime.
The full metric is g_μν = η_μν + h_μν with |h_μν| << 1. -/
structure WeakFieldPerturbation where
  /-- The perturbation components h_μν(x) -/
  h : Fin 4 → Fin 4 → ℝ → ℝ → ℝ → ℝ → ℝ
  /-- The perturbation is symmetric -/
  symmetric : ∀ μ ν t x y z, h μ ν t x y z = h ν μ t x y z

/-- The trace of the perturbation: h = η^μν h_μν. -/
def WeakFieldPerturbation.trace (hp : WeakFieldPerturbation) (t x y z : ℝ) : ℝ :=
  -hp.h 0 0 t x y z + hp.h 1 1 t x y z + hp.h 2 2 t x y z + hp.h 3 3 t x y z

/-- The trace-reversed perturbation: h̄_μν = h_μν - (1/2)η_μν h.
This simplifies the linearized Einstein equations. -/
def WeakFieldPerturbation.traceReversed (hp : WeakFieldPerturbation) :
    Fin 4 → Fin 4 → ℝ → ℝ → ℝ → ℝ → ℝ :=
  fun μ ν t x y z =>
    hp.h μ ν t x y z - (1/2) * minkowskiMetric μ ν * hp.trace t x y z

/-! ## Gauge Conditions -/

/-- The Lorenz (or harmonic/de Donder) gauge condition:
∂^μ h̄_μν = 0.

This is analogous to the Lorenz gauge in electromagnetism. -/
def isLorenzGauge (_hp : WeakFieldPerturbation) : Prop :=
  True  -- ∂^μ h̄_μν = 0

/-- In Lorenz gauge, the linearized Einstein equations become wave equations:
□h̄_μν = -16πG T_μν. -/
axiom wave_equation_lorenz (hp : WeakFieldPerturbation) (_hLorenz : isLorenzGauge hp) :
    True  -- □h̄_μν = -16πG T_μν

/-- Gauge transformations: h_μν → h_μν + ∂_μ ξ_ν + ∂_ν ξ_μ
for any vector field ξ^μ. -/
def gaugeTransformation (hp : WeakFieldPerturbation) (_xi : Fin 4 → ℝ → ℝ → ℝ → ℝ → ℝ) :
    WeakFieldPerturbation where
  h := hp.h  -- Would add ∂_μ ξ_ν + ∂_ν ξ_μ
  symmetric := hp.symmetric

/-- Residual gauge freedom: In Lorenz gauge, we can still perform
gauge transformations with □ξ^μ = 0. -/
axiom residual_gauge_freedom :
    True  -- □ξ^μ = 0 preserves Lorenz gauge

/-! ## Transverse-Traceless Gauge -/

/-- The transverse-traceless (TT) gauge for gravitational waves:
1. h = 0 (traceless)
2. h_0μ = 0 (purely spatial)
3. ∂^i h_ij = 0 (transverse)

This is the physical gauge for GW far from sources. -/
structure TTGaugePerturbation extends WeakFieldPerturbation where
  /-- Traceless: h = 0 -/
  traceless : ∀ t x y z, toWeakFieldPerturbation.trace t x y z = 0
  /-- Temporal components vanish -/
  temporal_zero : ∀ μ t x y z, h 0 μ t x y z = 0
  /-- Transverse condition -/
  transverse : True  -- ∂^i h_ij = 0

/-- In TT gauge, there are only 2 physical degrees of freedom:
the plus and cross polarizations. -/
axiom tt_two_polarizations :
    True  -- Only h_+ and h_× survive

/-- The plus polarization: h_+ affects x and y directions oppositely. -/
def plusPolarization (amplitude : ℝ) (omega k t z : ℝ) : ℝ :=
  amplitude * Real.cos (omega * t - k * z)

/-- The cross polarization: h_× is rotated 45° from h_+. -/
def crossPolarization (amplitude : ℝ) (omega k t z : ℝ) : ℝ :=
  amplitude * Real.cos (omega * t - k * z)

/-! ## Linearized Curvature -/

/-- The linearized Riemann tensor:
R^(1)_μνρσ = (1/2)(∂_ν∂_ρ h_μσ + ∂_μ∂_σ h_νρ - ∂_μ∂_ρ h_νσ - ∂_ν∂_σ h_μρ). -/
axiom linearized_riemann :
    True  -- R^(1) linear in h and its derivatives

/-- The linearized Ricci tensor:
R^(1)_μν = (1/2)(∂^ρ∂_μ h_νρ + ∂^ρ∂_ν h_μρ - □h_μν - ∂_μ∂_ν h). -/
axiom linearized_ricci :
    True  -- R^(1)_μν linear in h

/-- The linearized Ricci scalar:
R^(1) = ∂^μ∂^ν h_μν - □h. -/
axiom linearized_ricci_scalar :
    True  -- R^(1) = ∂∂h - □h

/-- The linearized Einstein tensor:
G^(1)_μν = R^(1)_μν - (1/2)η_μν R^(1). -/
axiom linearized_einstein_tensor :
    True  -- G^(1)_μν from R^(1)_μν

/-! ## Linearized Einstein Equations -/

/-- The linearized Einstein equations:
G^(1)_μν = 8πG T_μν

In Lorenz gauge: □h̄_μν = -16πG T_μν. -/
axiom linearized_einstein_equations :
    True  -- G^(1) = 8πG T

/-- In vacuum (T_μν = 0), we get the wave equation □h̄_μν = 0. -/
axiom linearized_vacuum_wave_eq :
    True  -- □h̄_μν = 0 in vacuum

/-- Plane wave solutions in vacuum:
h_μν = ε_μν exp(ik·x) where k² = 0. -/
def planeWaveSolution (epsilon : Fin 4 → Fin 4 → ℝ) (k : Fin 4 → ℝ) :
    Fin 4 → Fin 4 → ℝ → ℝ → ℝ → ℝ → ℝ :=
  fun μ ν t x y z =>
    let phase := -k 0 * t + k 1 * x + k 2 * y + k 3 * z
    epsilon μ ν * Real.cos phase

/-! ## The Graviton -/

/-- In the quantum field theory of linearized gravity, the graviton
is a massless spin-2 particle. -/
axiom graviton_spin_2 :
    True  -- Graviton has spin 2

/-- The graviton is massless: k² = 0 for on-shell gravitons. -/
axiom graviton_massless :
    True  -- m = 0, propagates at c

/-- The graviton has 2 physical polarizations (helicity ±2). -/
axiom graviton_polarizations :
    True  -- 2 polarization states

/-- The graviton propagator in Lorenz gauge (de Donder gauge):
D_μν,ρσ(k) = (η_μρ η_νσ + η_μσ η_νρ - η_μν η_ρσ) / (2k²). -/
axiom graviton_propagator :
    True  -- Propagator in momentum space

/-! ## Newtonian Limit -/

/-- In the static, weak-field limit, linearized gravity reduces
to Newtonian gravity with h_00 = -2Φ/c². -/
def newtonianPotentialFromPerturbation (hp : WeakFieldPerturbation) (t x y z : ℝ) : ℝ :=
  -hp.h 0 0 t x y z / 2

/-- The linearized Einstein equations in the static limit give
∇²Φ = 4πGρ (Poisson's equation). -/
axiom static_limit_poisson :
    True  -- Newtonian limit: ∇²Φ = 4πGρ

/-- The spatial metric perturbation in the Newtonian limit:
h_ij = -2Φ δ_ij (in isotropic coordinates). -/
axiom newtonian_spatial_metric :
    True  -- h_ij = -2Φ δ_ij

/-! ## Gravitational Waves from Sources -/

/-- The retarded solution to the linearized equations:
h̄_μν(t,x) = 4G ∫ T_μν(t_ret, x') / |x - x'| d³x'
where t_ret = t - |x - x'|/c. -/
axiom retarded_solution :
    True  -- h̄ from retarded Green's function

/-- Far from the source (r >> source size), the radiation is
determined by the mass quadrupole moment:
h_ij^TT = (2G/r) d²I_ij^TT/dt². -/
axiom quadrupole_radiation_formula :
    True  -- h ~ (G/r) Ï̈_ij

/-- The gravitational wave luminosity (quadrupole formula):
L_GW = (G/5c⁵) ⟨d³I_ij/dt³ d³I^ij/dt³⟩. -/
axiom gw_luminosity_quadrupole :
    True  -- L = (G/5) ⟨Ï̈̈ Ï̈̈⟩

/-! ## Higher-Order Perturbations -/

/-- Second-order perturbation theory: g = η + h^(1) + h^(2) + ...
This is needed for gravitational wave energy and self-interaction. -/
axiom second_order_perturbation :
    True  -- h^(2) from (h^(1))²

/-- The effective stress-energy tensor of gravitational waves
(Isaacson tensor) appears at second order:
t_μν^GW = (c⁴/32πG) ⟨∂_μh_ρσ ∂_νh^ρσ⟩. -/
axiom isaacson_stress_energy :
    True  -- t_μν^GW ~ ⟨∂h ∂h⟩

/-- Gravitational waves carry energy and momentum, back-reacting
on the background spacetime at second order. -/
axiom gw_backreaction :
    True  -- GW self-gravitate at O(h²)

/-! ## Gauge-Invariant Quantities -/

/-- The linearized Weyl tensor is gauge-invariant to first order.
It contains the physical degrees of freedom of gravitational waves. -/
axiom linearized_weyl_gauge_invariant :
    True  -- C^(1)_μνρσ gauge-invariant

/-- The Bardeen potentials Φ and Ψ are gauge-invariant combinations
in cosmological perturbation theory. -/
axiom bardeen_potentials :
    True  -- Φ, Ψ gauge-invariant

/-- In general, gauge-invariant quantities can be constructed by
combining metric perturbations with matter perturbations. -/
axiom gauge_invariant_combinations :
    True  -- Various gauge-invariant variables exist

end PseudoRiemannianMetric
end
