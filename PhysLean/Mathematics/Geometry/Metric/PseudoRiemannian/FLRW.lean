/-
Copyright (c) 2025 PhysLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PhysLean Contributors
-/

import PhysLean.Mathematics.Geometry.Metric.PseudoRiemannian.Einstein
import PhysLean.Mathematics.Geometry.Metric.PseudoRiemannian.EnergyConditions
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Friedmann-Lemaitre-Robertson-Walker Cosmology

This file defines the FLRW metric and the Friedmann equations, which describe
the dynamics of a homogeneous and isotropic universe.

## Main Definitions

* `FLRWData`: Parameters for the FLRW metric (scale factor, curvature)
* `SpatialCurvature`: The three types of spatial geometry (flat, spherical, hyperbolic)
* `FriedmannEquation1`: The first Friedmann equation relating H² to density

## Physical Interpretation

The FLRW metric describes a universe that is:
- Spatially homogeneous: no preferred location
- Spatially isotropic: no preferred direction
- Expanding (or contracting) uniformly: scale factor a(t)

In comoving coordinates (t, r, θ, φ), the metric is:
  ds² = -dt² + a(t)² [dr²/(1-kr²) + r² dΩ²]

where:
- a(t) is the scale factor
- k = +1, 0, -1 for closed, flat, open universes

## References

* Misner, Thorne, Wheeler, "Gravitation" (1973), Chapters 27-28
* Weinberg, "Gravitation and Cosmology" (1972)
* Wald, "General Relativity" (1984), Chapter 5
-/

noncomputable section

namespace PseudoRiemannianMetric

/-! ## Spatial Curvature -/

/-- The three types of spatial curvature for homogeneous isotropic spaces.
These correspond to the maximally symmetric 3-spaces:
- `flat`: Euclidean R³, k = 0
- `spherical`: 3-sphere S³, k = +1
- `hyperbolic`: Hyperbolic space H³, k = -1 -/
inductive SpatialCurvature
  | flat       -- k = 0, Euclidean geometry
  | spherical  -- k = +1, positive curvature (closed universe)
  | hyperbolic -- k = -1, negative curvature (open universe)

/-- The curvature parameter k in {-1, 0, +1}. -/
def SpatialCurvature.k : SpatialCurvature → ℤ
  | .flat => 0
  | .spherical => 1
  | .hyperbolic => -1

/-- Flat has k = 0. -/
lemma SpatialCurvature.flat_k : SpatialCurvature.flat.k = 0 := rfl

/-- Spherical has k = 1. -/
lemma SpatialCurvature.spherical_k : SpatialCurvature.spherical.k = 1 := rfl

/-- Hyperbolic has k = -1. -/
lemma SpatialCurvature.hyperbolic_k : SpatialCurvature.hyperbolic.k = -1 := rfl

/-! ## FLRW Metric Structure -/

/-- Data specifying an FLRW cosmology.
This includes the scale factor as a function of cosmic time and the spatial curvature. -/
structure FLRWData where
  /-- The scale factor a(t) as a function of cosmic time -/
  scaleFactor : ℝ → ℝ
  /-- The scale factor is positive -/
  scaleFactor_pos : ∀ t, scaleFactor t > 0
  /-- The spatial curvature type -/
  curvature : SpatialCurvature

/-- The Hubble parameter H(t) = (da/dt) / a(t). -/
def FLRWData.hubbleParameter (F : FLRWData) (da_dt : ℝ → ℝ) (t : ℝ) : ℝ :=
  da_dt t / F.scaleFactor t

/-- The Hubble parameter squared. -/
def FLRWData.hubbleParameterSq (F : FLRWData) (da_dt : ℝ → ℝ) (t : ℝ) : ℝ :=
  (F.hubbleParameter da_dt t)^2

/-- FLRW comoving coordinates: (t, r, θ, φ). -/
structure FLRWCoords where
  /-- Cosmic time -/
  t : ℝ
  /-- Comoving radial coordinate -/
  r : ℝ
  /-- Polar angle -/
  theta : ℝ
  /-- Azimuthal angle -/
  phi : ℝ
  /-- r is non-negative -/
  r_nonneg : r ≥ 0

/-- The spatial metric factor f_k(r) = 1/(1 - kr²) for the radial part. -/
def spatialRadialFactor (k : SpatialCurvature) (r : ℝ) : ℝ :=
  1 / (1 - k.k * r^2)

/-- The FLRW metric components in comoving coordinates.
ds² = -dt² + a(t)² [f_k(r) dr² + r² dΩ²] -/
def flrwMetricComponents (F : FLRWData) (coords : FLRWCoords) :
    ℝ × ℝ × ℝ × ℝ :=
  let a := F.scaleFactor coords.t
  let f := spatialRadialFactor F.curvature coords.r
  (-1,                           -- g_tt = -1
   a^2 * f,                      -- g_rr = a²/(1-kr²)
   a^2 * coords.r^2,             -- g_θθ = a² r²
   a^2 * coords.r^2 * (Real.sin coords.theta)^2)  -- g_φφ = a² r² sin²θ

/-- The g_tt component is always -1. -/
lemma flrw_gtt (F : FLRWData) (coords : FLRWCoords) :
    (flrwMetricComponents F coords).1 = -1 := rfl

/-! ## Friedmann Equations -/

/-- The first Friedmann equation relates the Hubble parameter to energy density:
H² = (8πG/3)ρ - k/a² + Λ/3

In geometric units (8πG = 1):
H² = ρ/3 - k/a² + Λ/3 -/
structure FriedmannEquation1 (F : FLRWData) where
  /-- Energy density as a function of time -/
  rho : ℝ → ℝ
  /-- Cosmological constant -/
  Lambda : ℝ
  /-- Time derivative of scale factor -/
  da_dt : ℝ → ℝ
  /-- The first Friedmann equation holds -/
  equation : ∀ t,
    (F.hubbleParameter da_dt t)^2 =
      rho t / 3 - F.curvature.k / (F.scaleFactor t)^2 + Lambda / 3

/-- The second Friedmann equation (acceleration equation):
d²a/dt² / a = -(4πG/3)(ρ + 3p) + Λ/3

In geometric units:
d²a/dt² / a = -(ρ + 3p)/6 + Λ/3 -/
structure FriedmannEquation2 (F : FLRWData) where
  /-- Energy density -/
  rho : ℝ → ℝ
  /-- Pressure -/
  p : ℝ → ℝ
  /-- Cosmological constant -/
  Lambda : ℝ
  /-- Second derivative of scale factor -/
  d2a_dt2 : ℝ → ℝ
  /-- The acceleration equation holds -/
  equation : ∀ t,
    d2a_dt2 t / F.scaleFactor t = -(rho t + 3 * p t) / 6 + Lambda / 3

/-! ## Cosmological Parameters -/

/-- The critical density ρ_c = 3H²/(8πG) at which the universe is spatially flat.
In geometric units: ρ_c = 3H² -/
def criticalDensity (H : ℝ) : ℝ := 3 * H^2

/-- The critical density is non-negative. -/
lemma criticalDensity_nonneg (H : ℝ) : criticalDensity H ≥ 0 := by
  unfold criticalDensity
  apply mul_nonneg; norm_num; exact sq_nonneg H

/-- The density parameter Ω = ρ/ρ_c for any component.
Ω = 1 corresponds to critical density. -/
def densityParameter (rho H : ℝ) : ℝ := rho / criticalDensity H

/-- The curvature parameter Ω_k = -k/(aH)². -/
def curvatureParameter (k : SpatialCurvature) (a H : ℝ) : ℝ :=
  -k.k / (a * H)^2

/-- The cosmological constant parameter Ω_Λ = Λ/(3H²). -/
def lambdaParameter (Lambda H : ℝ) : ℝ := Lambda / (3 * H^2)

/-- For flat curvature, Ω_k = 0. -/
lemma curvatureParameter_flat (a H : ℝ) :
    curvatureParameter SpatialCurvature.flat a H = 0 := by
  unfold curvatureParameter
  simp [SpatialCurvature.flat_k]

/-! ## Equation of State -/

/-- Equation of state parameter w = p/ρ for different matter types:
- w = 0: non-relativistic matter (dust)
- w = 1/3: radiation
- w = -1: cosmological constant
- w < -1/3: accelerating expansion -/
def equationOfState (p rho : ℝ) : ℝ := p / rho

/-- Matter equation of state. -/
def matterEOS : ℝ := 0

/-- Radiation equation of state. -/
def radiationEOS : ℝ := 1/3

/-- Cosmological constant equation of state. -/
def cosmologicalConstantEOS : ℝ := -1

/-! ## Special FLRW Solutions -/

/-- De Sitter space: exponentially expanding universe with Λ > 0, ρ = p = 0, k = 0.
a(t) = a₀ exp(Ht) where H = √(Λ/3). -/
def isDeSitter (F : FLRWData) (Lambda : ℝ) : Prop :=
  F.curvature = SpatialCurvature.flat ∧
  Lambda > 0 ∧
  ∃ a_0 H, H = Real.sqrt (Lambda / 3) ∧ ∀ t, F.scaleFactor t = a_0 * Real.exp (H * t)

/-- Einstein static universe: static solution with Λ > 0, k = +1 (unstable). -/
def isEinsteinStatic (F : FLRWData) : Prop :=
  F.curvature = SpatialCurvature.spherical ∧
  ∃ a_0, ∀ t, F.scaleFactor t = a_0

/-- Milne universe: empty expanding universe, equivalent to flat Minkowski in different coords. -/
def isMilne (F : FLRWData) : Prop :=
  F.curvature = SpatialCurvature.hyperbolic ∧
  ∃ t_0, ∀ t, F.scaleFactor t = t - t_0

/-- Matter-dominated Einstein-de Sitter universe (flat, no Λ, matter only).
a(t) ∝ t^(2/3). -/
def isEinsteinDeSitter (F : FLRWData) : Prop :=
  F.curvature = SpatialCurvature.flat ∧
  ∃ C, C > 0 ∧ ∀ t, t > 0 → F.scaleFactor t = C * Real.rpow t (2/3)

/-- Radiation-dominated universe: a(t) ∝ t^(1/2). -/
def isRadiationDominated (F : FLRWData) : Prop :=
  ∃ C, ∀ t, t > 0 → F.scaleFactor t = C * Real.sqrt t

/-! ## Hubble Law and Redshift -/

/-- Cosmological redshift: wavelength stretched by expansion.
1 + z = a(t_obs)/a(t_emit) = a₀/a(t) -/
def cosmologicalRedshift (F : FLRWData) (t_emit t_obs : ℝ) : ℝ :=
  F.scaleFactor t_obs / F.scaleFactor t_emit - 1

/-- The redshift is positive for expanding universe when t_obs > t_emit. -/
lemma redshift_pos_expanding (F : FLRWData) (t_emit t_obs : ℝ)
    (h_expand : F.scaleFactor t_obs > F.scaleFactor t_emit) :
    cosmologicalRedshift F t_emit t_obs > 0 := by
  unfold cosmologicalRedshift
  have h1 : F.scaleFactor t_emit > 0 := F.scaleFactor_pos t_emit
  have h2 : F.scaleFactor t_obs / F.scaleFactor t_emit > 1 := by
    have := (one_lt_div h1).mpr h_expand
    exact this
  linarith

/-- The Hubble horizon: distance at which recession velocity equals speed of light.
d_H = c/H (in natural units, just 1/H) -/
def hubbleHorizon (H : ℝ) : ℝ := 1 / H

/-- The Hubble horizon is positive for positive H. -/
lemma hubbleHorizon_pos (H : ℝ) (hH : H > 0) : hubbleHorizon H > 0 := by
  unfold hubbleHorizon
  exact one_div_pos.mpr hH

/-! ## Number of Killing Vectors -/

/-- FLRW spacetime has 6 spacelike Killing vectors (maximally symmetric spatial slices):
3 translations + 3 rotations. -/
def flrwKillingCount : ℕ := 6

end PseudoRiemannianMetric
end
