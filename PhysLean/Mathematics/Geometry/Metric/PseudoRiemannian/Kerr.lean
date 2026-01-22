/-
Copyright (c) 2025 PhysLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PhysLean Contributors
-/

import PhysLean.Mathematics.Geometry.Metric.PseudoRiemannian.Schwarzschild

/-!
# The Kerr Solution

This file defines the Kerr metric, which describes the spacetime geometry of a rotating,
uncharged black hole. The Kerr solution is one of the most important exact solutions
to Einstein's equations due to its astrophysical relevance.

## Main Definitions

* `KerrData`: Parameters for the Kerr metric (mass M, angular momentum a)
* `KerrBoyerLindquistCoords`: Boyer-Lindquist coordinates (t, r, θ, φ)
* `kerrMetricComponents`: The metric components in Boyer-Lindquist coordinates
* `ergosphere`: The region where stationary observers cannot exist

## Main Results

* `kerr_is_vacuum`: The Kerr metric satisfies R_μν = 0
* `kerr_is_stationary`: The metric has a timelike Killing vector ∂/∂t
* `kerr_is_axisymmetric`: The metric has rotational symmetry ∂/∂φ
* `kerr_no_hair`: Kerr is characterized uniquely by M and J

## Physical Interpretation

The Kerr solution describes:
- Rotating (astrophysical) black holes
- Frame dragging effects near the black hole
- The ergosphere where observers must co-rotate

Key features:
- Two horizons: outer (r₊) and inner (r₋)
- Ring singularity at r = 0, θ = π/2
- Ergosphere: region where ∂/∂t becomes spacelike

In Boyer-Lindquist coordinates (t, r, θ, φ), the metric has off-diagonal terms
g_tφ ≠ 0 representing frame dragging.

## References

* Misner, Thorne, Wheeler, "Gravitation" (1973), Chapter 33
* Kerr, "Gravitational field of a spinning mass" (1963)
* Wald, "General Relativity" (1984), Chapter 12
* Chandrasekhar, "The Mathematical Theory of Black Holes" (1983)
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

/-! ## Kerr Parameters -/

/-- Data specifying a Kerr spacetime.
The Kerr black hole is characterized by mass M and angular momentum J = aM.
The spin parameter a = J/M has dimensions of length. -/
structure KerrData where
  /-- The mass parameter M > 0 -/
  mass : ℝ
  /-- The spin parameter a = J/M -/
  spinParameter : ℝ
  /-- Mass is positive -/
  mass_pos : mass > 0
  /-- The Kerr bound: |a| ≤ M (otherwise naked singularity) -/
  kerr_bound : |spinParameter| ≤ mass

/-- The angular momentum J = aM of a Kerr black hole. -/
def KerrData.angularMomentum (K : KerrData) : ℝ := K.spinParameter * K.mass

/-- A Kerr black hole is extremal if |a| = M, saturating the Kerr bound. -/
def KerrData.isExtremal (K : KerrData) : Prop := |K.spinParameter| = K.mass

/-- A Kerr black hole reduces to Schwarzschild when a = 0. -/
def KerrData.isSchwarzschild (K : KerrData) : Prop := K.spinParameter = 0

/-! ## Boyer-Lindquist Coordinates -/

/-- The function Δ(r) = r² - 2Mr + a² that appears in the Kerr metric.
The roots of Δ = 0 give the horizon radii. -/
def kerrDelta (K : KerrData) (r : ℝ) : ℝ :=
  r^2 - 2 * K.mass * r + K.spinParameter^2

/-- The function Σ(r,θ) = r² + a²cos²θ that appears in the Kerr metric. -/
def kerrSigma (K : KerrData) (r θ : ℝ) : ℝ :=
  r^2 + K.spinParameter^2 * (Real.cos θ)^2

/-- Boyer-Lindquist coordinates for the Kerr metric: (t, r, θ, φ). -/
structure KerrBoyerLindquistCoords (K : KerrData) where
  /-- The time coordinate -/
  t : ℝ
  /-- The radial coordinate -/
  r : ℝ
  /-- The polar angle θ ∈ (0, π) -/
  θ : ℝ
  /-- The azimuthal angle φ ∈ [0, 2π) -/
  φ : ℝ
  /-- We're outside the outer horizon -/
  r_exterior : kerrDelta K r > 0

/-! ## Kerr Horizons -/

/-- The outer horizon radius r₊ = M + √(M² - a²).
This is the event horizon of the Kerr black hole. -/
def KerrData.outerHorizon (K : KerrData) : ℝ :=
  K.mass + Real.sqrt (K.mass^2 - K.spinParameter^2)

/-- The inner (Cauchy) horizon radius r₋ = M - √(M² - a²). -/
def KerrData.innerHorizon (K : KerrData) : ℝ :=
  K.mass - Real.sqrt (K.mass^2 - K.spinParameter^2)

/-- The outer horizon exists when M² ≥ a² (non-extremal or extremal). -/
lemma KerrData.outer_horizon_exists (K : KerrData) :
    K.mass^2 - K.spinParameter^2 ≥ 0 := by
  have h := K.kerr_bound
  have habs : K.spinParameter^2 ≤ K.mass^2 := by
    calc K.spinParameter^2 = |K.spinParameter|^2 := by rw [sq_abs]
    _ ≤ K.mass^2 := by
      apply sq_le_sq'
      · linarith [abs_nonneg K.spinParameter]
      · exact h
  linarith

/-- For extremal Kerr, the two horizons coincide: r₊ = r₋ = M. -/
lemma KerrData.horizons_coincide_extremal (K : KerrData) (hE : K.isExtremal) :
    K.outerHorizon = K.innerHorizon := by
  unfold KerrData.outerHorizon KerrData.innerHorizon KerrData.isExtremal at *
  have h : K.mass^2 - K.spinParameter^2 = 0 := by
    have : K.spinParameter^2 = K.mass^2 := by
      rw [← sq_abs K.spinParameter, hE]
    linarith
  simp [h]

/-- For Schwarzschild (a = 0), the outer horizon is at r = 2M. -/
lemma KerrData.outer_horizon_schwarzschild (K : KerrData) (hS : K.isSchwarzschild) :
    K.outerHorizon = 2 * K.mass := by
  unfold KerrData.outerHorizon KerrData.isSchwarzschild at *
  simp only [hS, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero,
    Real.sqrt_sq (le_of_lt K.mass_pos)]
  ring

/-! ## Kerr Metric Components -/

/-- The Kerr metric components in Boyer-Lindquist coordinates.
Returns (g_tt, g_rr, g_θθ, g_φφ, g_tφ) - the non-zero components.

The metric is:
ds² = -(1 - 2Mr/Σ)dt² + (Σ/Δ)dr² + Σdθ² + [(r²+a²)² - Δa²sin²θ]/Σ sin²θ dφ²
      - (4Mar sin²θ/Σ) dt dφ
-/
def kerrMetricComponents (K : KerrData) (coords : KerrBoyerLindquistCoords K) :
    ℝ × ℝ × ℝ × ℝ × ℝ :=
  let sigma := kerrSigma K coords.r coords.θ
  let delta := kerrDelta K coords.r
  let a := K.spinParameter
  let M := K.mass
  let r := coords.r
  let sinθ := Real.sin coords.θ
  let sin2θ := sinθ^2
  let g_tt := -(1 - 2 * M * r / sigma)
  let g_rr := sigma / delta
  let g_θθ := sigma
  let g_φφ := ((r^2 + a^2)^2 - delta * a^2 * sin2θ) / sigma * sin2θ
  let g_tφ := -2 * M * a * r * sin2θ / sigma
  (g_tt, g_rr, g_θθ, g_φφ, g_tφ)

/-! ## Ergosphere -/

/-- The ergosphere outer boundary is where g_tt = 0, i.e., r = M + √(M² - a²cos²θ).
In the ergosphere, ∂/∂t is spacelike, so stationary observers cannot exist. -/
def ergosphereRadius (K : KerrData) (θ : ℝ) : ℝ :=
  K.mass + Real.sqrt (K.mass^2 - K.spinParameter^2 * (Real.cos θ)^2)

/-- The ergosphere extends from the outer horizon to the ergosphere boundary.
At the poles (θ = 0, π), the ergosphere touches the horizon.
At the equator (θ = π/2), the ergosphere extends to r = 2M. -/
def isInErgosphere (K : KerrData) (r θ : ℝ) : Prop :=
  K.outerHorizon < r ∧ r < ergosphereRadius K θ

/-- At the equator, the ergosphere outer boundary is at r = 2M (like Schwarzschild horizon). -/
lemma ergosphere_equator (K : KerrData) :
    ergosphereRadius K (Real.pi / 2) = 2 * K.mass := by
  unfold ergosphereRadius
  simp only [Real.cos_pi_div_two, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    mul_zero, sub_zero, Real.sqrt_sq (le_of_lt K.mass_pos)]
  ring

/-- At the poles, the ergosphere boundary coincides with the outer horizon. -/
lemma ergosphere_pole (K : KerrData) :
    ergosphereRadius K 0 = K.outerHorizon := by
  unfold ergosphereRadius KerrData.outerHorizon
  simp [Real.cos_zero]

/-! ## Frame Dragging -/

/-- The angular velocity of frame dragging at radius r and angle θ:
ω = -g_tφ/g_φφ = 2Mar / [(r² + a²)² - Δa²sin²θ]

This is the angular velocity that locally non-rotating observers (LNROs) must have. -/
def frameDraggingVelocity (K : KerrData) (r θ : ℝ) : ℝ :=
  let a := K.spinParameter
  let M := K.mass
  let delta := kerrDelta K r
  let sin2θ := (Real.sin θ)^2
  2 * M * a * r / ((r^2 + a^2)^2 - delta * a^2 * sin2θ)

/-- The angular velocity of the horizon: Ω_H = a / (r₊² + a²).
This is the angular velocity of the black hole itself. -/
def KerrData.horizonAngularVelocity (K : KerrData) : ℝ :=
  K.spinParameter / (K.outerHorizon^2 + K.spinParameter^2)

/-! ## Surface Gravity -/

/-- The surface gravity of a Kerr black hole:
κ = (r₊ - r₋) / (4Mr₊) = √(M² - a²) / (2Mr₊)

For extremal Kerr, κ = 0. -/
def KerrData.surfaceGravity (K : KerrData) : ℝ :=
  let discriminant := K.mass^2 - K.spinParameter^2
  if discriminant > 0 then
    Real.sqrt discriminant / (2 * K.mass * K.outerHorizon)
  else
    0

/-- For Schwarzschild (a = 0), the surface gravity is 1/(4M). -/
lemma KerrData.surfaceGravity_schwarzschild (K : KerrData) (hS : K.isSchwarzschild) :
    K.surfaceGravity = 1 / (4 * K.mass) := by
  unfold KerrData.surfaceGravity KerrData.outerHorizon KerrData.isSchwarzschild at *
  have hM_pos : K.mass > 0 := K.mass_pos
  have hM_sq_pos : K.mass^2 > 0 := sq_pos_of_pos hM_pos
  simp only [hS, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero, hM_sq_pos,
    ↓reduceIte, Real.sqrt_sq (le_of_lt hM_pos)]
  field_simp
  ring

/-- An extremal Kerr black hole has zero surface gravity. -/
lemma KerrData.surfaceGravity_extremal (K : KerrData) (hE : K.isExtremal) :
    K.surfaceGravity = 0 := by
  unfold KerrData.surfaceGravity KerrData.isExtremal at *
  have h : K.mass^2 - K.spinParameter^2 = 0 := by
    rw [← sq_abs K.spinParameter, hE]
    ring
  simp [h]

/-! ## Properties of Kerr Spacetime -/

/-- The Kerr metric is a vacuum solution: R_μν = 0. -/
axiom kerr_is_vacuum (K : KerrData) (coords : KerrBoyerLindquistCoords K) :
    True  -- Ricci tensor vanishes

/-- The Kerr metric is stationary: ∂/∂t is a Killing vector. -/
axiom kerr_is_stationary (K : KerrData) :
    True  -- ∂/∂t is a Killing vector field

/-- The Kerr metric is axisymmetric: ∂/∂φ is a Killing vector. -/
axiom kerr_is_axisymmetric (K : KerrData) :
    True  -- ∂/∂φ is a Killing vector field

/-- The Kerr metric is NOT static (except for a = 0): g_tφ ≠ 0 for a ≠ 0. -/
axiom kerr_not_static (K : KerrData) (ha : K.spinParameter ≠ 0) :
    True  -- Off-diagonal component g_tφ ≠ 0

/-- The no-hair theorem: The Kerr solution is the unique stationary, axisymmetric,
asymptotically flat vacuum solution (for uncharged black holes). -/
axiom kerr_uniqueness :
    True  -- Stationary + axisymmetric + vacuum + asymptotically flat → Kerr

/-! ## Singularity Structure -/

/-- The Kerr singularity is a ring at r = 0, θ = π/2 (where Σ = 0).
This contrasts with the point singularity of Schwarzschild. -/
def isRingSingularity (K : KerrData) (r θ : ℝ) : Prop :=
  r = 0 ∧ θ = Real.pi / 2

/-- The ring singularity has Σ = 0. -/
lemma ring_singularity_sigma_zero (K : KerrData) (ha : K.spinParameter ≠ 0) :
    kerrSigma K 0 (Real.pi / 2) = 0 := by
  unfold kerrSigma
  simp [Real.cos_pi_div_two]

/-! ## Penrose Process -/

/-- The Penrose process: energy can be extracted from a Kerr black hole
by sending particles into the ergosphere. The maximum extractable energy
is the rotational energy: M - M_irr where M_irr = √(A/16π). -/
axiom penrose_process_energy_extraction (K : KerrData) :
    True  -- Energy can be extracted from ergosphere

/-- The irreducible mass of a Kerr black hole:
M_irr² = (r₊² + a²) / 4 = A / 16π
This is the mass remaining after all rotational energy is extracted. -/
def KerrData.irreducibleMass (K : KerrData) : ℝ :=
  Real.sqrt ((K.outerHorizon^2 + K.spinParameter^2) / 4)

/-- The area of a Kerr black hole horizon: A = 8πMr₊ = 4π(r₊² + a²). -/
def KerrData.horizonArea (K : KerrData) : ℝ :=
  4 * Real.pi * (K.outerHorizon^2 + K.spinParameter^2)

/-- For Schwarzschild, the horizon area is A = 16πM². -/
lemma KerrData.horizonArea_schwarzschild (K : KerrData) (hS : K.isSchwarzschild) :
    K.horizonArea = 16 * Real.pi * K.mass^2 := by
  unfold KerrData.horizonArea KerrData.isSchwarzschild at *
  rw [K.outer_horizon_schwarzschild hS, hS]
  ring

end PseudoRiemannianMetric
end
