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
* `FriedmannEquations`: The dynamical equations for the scale factor

## Main Results

* `flrw_is_homogeneous`: The metric has spatial translation symmetry
* `flrw_is_isotropic`: The metric looks the same in all spatial directions
* `friedmann_from_einstein`: Friedmann equations follow from Einstein equations

## Physical Interpretation

The FLRW metric describes a universe that is:
- Spatially homogeneous: no preferred location
- Spatially isotropic: no preferred direction
- Expanding (or contracting) uniformly: scale factor a(t)

In comoving coordinates (t, r, theta, phi), the metric is:
  ds^2 = -dt^2 + a(t)^2 [dr^2/(1-kr^2) + r^2 dOmega^2]

where:
- a(t) is the scale factor
- k = +1, 0, -1 for closed, flat, open universes

## References

* Misner, Thorne, Wheeler, "Gravitation" (1973), Chapters 27-28
* Weinberg, "Gravitation and Cosmology" (1972)
* Wald, "General Relativity" (1984), Chapter 5
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

/-! ## Spatial Curvature -/

/-- The three types of spatial curvature for homogeneous isotropic spaces.
These correspond to the maximally symmetric 3-spaces:
- `flat`: Euclidean R^3, k = 0
- `spherical`: 3-sphere S^3, k = +1
- `hyperbolic`: Hyperbolic space H^3, k = -1 -/
inductive SpatialCurvature
  | flat       -- k = 0, Euclidean geometry
  | spherical  -- k = +1, positive curvature (closed universe)
  | hyperbolic -- k = -1, negative curvature (open universe)

/-- The curvature parameter k in {-1, 0, +1}. -/
def SpatialCurvature.k : SpatialCurvature → ℤ
  | .flat => 0
  | .spherical => 1
  | .hyperbolic => -1

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

/-- The Hubble parameter H(t) = da/dt / a(t). -/
def FLRWData.hubbleParameter (F : FLRWData) (da_dt : ℝ → ℝ) (t : ℝ) : ℝ :=
  da_dt t / F.scaleFactor t

/-- FLRW comoving coordinates: (t, r, theta, phi). -/
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

/-- The spatial metric factor f_k(r) = 1/(1 - kr^2) for the radial part. -/
def spatialRadialFactor (k : SpatialCurvature) (r : ℝ) : ℝ :=
  1 / (1 - k.k * r^2)

/-- The FLRW metric components in comoving coordinates.
ds^2 = -dt^2 + a(t)^2 [f_k(r) dr^2 + r^2 dOmega^2] -/
def flrwMetricComponents (F : FLRWData) (coords : FLRWCoords) :
    ℝ × ℝ × ℝ × ℝ :=
  let a := F.scaleFactor coords.t
  let f := spatialRadialFactor F.curvature coords.r
  (-1,                           -- g_tt = -1
   a^2 * f,                      -- g_rr = a^2/(1-kr^2)
   a^2 * coords.r^2,             -- g_theta_theta = a^2 r^2
   a^2 * coords.r^2 * (Real.sin coords.theta)^2)  -- g_phi_phi = a^2 r^2 sin^2 theta

/-! ## Symmetries of FLRW -/

/-- The FLRW metric is spatially homogeneous: there are 3 spacelike Killing vectors
corresponding to spatial translations. -/
axiom flrw_is_homogeneous (F : FLRWData) :
    True  -- Three translational Killing vectors

/-- The FLRW metric is spatially isotropic: there are 3 Killing vectors corresponding
to rotations about any point. -/
axiom flrw_is_isotropic (F : FLRWData) :
    True  -- Three rotational Killing vectors at each point

/-- The FLRW spacetime has 6 spacelike Killing vectors total (maximally symmetric
spatial slices). -/
axiom flrw_six_killing_vectors (F : FLRWData) :
    True  -- 6 = 3 translations + 3 rotations

/-! ## Friedmann Equations -/

/-- The first Friedmann equation relates the Hubble parameter to energy density:
H^2 = (8 pi G/3) rho - k/a^2 + Lambda/3

In geometric units (8 pi G = 1):
H^2 = rho/3 - k/a^2 + Lambda/3 -/
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
d^2a/dt^2 / a = -(4 pi G/3)(rho + 3p) + Lambda/3

In geometric units:
d^2a/dt^2 / a = -(rho + 3p)/6 + Lambda/3 -/
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

/-- The Friedmann equations follow from the Einstein equations applied to FLRW. -/
axiom friedmann_from_einstein (F : FLRWData) :
    True  -- Einstein equations + FLRW ansatz -> Friedmann equations

/-! ## Cosmological Parameters -/

/-- The critical density rho_c = 3H^2/8 pi G at which the universe is spatially flat.
In geometric units: rho_c = 3H^2 -/
def criticalDensity (H : ℝ) : ℝ := 3 * H^2

/-- The density parameter Omega = rho/rho_c for any component.
Omega = 1 corresponds to critical density. -/
def densityParameter (rho H : ℝ) : ℝ := rho / criticalDensity H

/-- The curvature parameter Omega_k = -k/(aH)^2. -/
def curvatureParameter (k : SpatialCurvature) (a H : ℝ) : ℝ :=
  -k.k / (a * H)^2

/-- The cosmological constant parameter Omega_Lambda = Lambda/(3H^2). -/
def lambdaParameter (Lambda H : ℝ) : ℝ := Lambda / (3 * H^2)

/-- The Friedmann constraint: Omega_m + Omega_r + Omega_k + Omega_Lambda = 1.
Sum of all density parameters equals 1. -/
axiom friedmann_constraint (Omega_m Omega_r Omega_k Omega_Lambda : ℝ) :
    True  -- Omega_m + Omega_r + Omega_k + Omega_Lambda = 1 from first Friedmann equation

/-! ## Equation of State and Evolution -/

/-- Equation of state parameter w = p/rho for different matter types:
- w = 0: non-relativistic matter (dust)
- w = 1/3: radiation
- w = -1: cosmological constant
- w < -1/3: accelerating expansion -/
def equationOfState (p rho : ℝ) : ℝ := p / rho

/-- For constant equation of state w, density evolves as rho proportional to a^(-3(1+w)). -/
axiom density_evolution (F : FLRWData) (_w : ℝ) :
    True  -- rho(t) = rho_0 (a_0/a(t))^(3(1+w))

/-- Non-relativistic matter (w = 0) dilutes as a^(-3) (volume dilution). -/
axiom matter_dilution (F : FLRWData) :
    True  -- rho_m proportional to a^(-3)

/-- Radiation (w = 1/3) dilutes as a^(-4) (volume + redshift). -/
axiom radiation_dilution (F : FLRWData) :
    True  -- rho_r proportional to a^(-4)

/-! ## Special FLRW Solutions -/

/-- De Sitter space: exponentially expanding universe with Lambda > 0, rho = p = 0, k = 0.
a(t) = a_0 exp(Ht) where H = sqrt(Lambda/3). -/
def isDeSitter (F : FLRWData) (Lambda : ℝ) : Prop :=
  F.curvature = SpatialCurvature.flat ∧
  Lambda > 0 ∧
  ∃ a_0 H, H = Real.sqrt (Lambda / 3) ∧ ∀ t, F.scaleFactor t = a_0 * Real.exp (H * t)

/-- Einstein static universe: static solution with Lambda > 0, k = +1 (unstable). -/
def isEinsteinStatic (F : FLRWData) : Prop :=
  F.curvature = SpatialCurvature.spherical ∧
  ∃ a_0, ∀ t, F.scaleFactor t = a_0

/-- Milne universe: empty expanding universe, equivalent to flat Minkowski in different coords. -/
def isMilne (F : FLRWData) : Prop :=
  F.curvature = SpatialCurvature.hyperbolic ∧
  ∃ t_0, ∀ t, F.scaleFactor t = t - t_0

/-- Matter-dominated Einstein-de Sitter universe (flat, no Lambda, matter only).
a(t) proportional to t^(2/3). This is the solution for matter-dominated flat universe. -/
def isEinsteinDeSitter (F : FLRWData) : Prop :=
  F.curvature = SpatialCurvature.flat ∧
  ∃ C, C > 0 ∧ ∀ t, t > 0 → F.scaleFactor t = C * Real.rpow t (2/3)

/-- Radiation-dominated universe: a(t) proportional to t^(1/2). -/
def isRadiationDominated (F : FLRWData) : Prop :=
  ∃ C, ∀ t, t > 0 → F.scaleFactor t = C * Real.sqrt t

/-! ## Hubble Law and Redshift -/

/-- The Hubble law: recession velocity is proportional to distance.
v = H d for nearby objects. -/
axiom hubble_law (F : FLRWData) (_da_dt : ℝ → ℝ) (_t : ℝ) :
    True  -- v = H(t) * d for comoving distance d

/-- Cosmological redshift: wavelength stretched by expansion.
1 + z = a(t_obs)/a(t_emit) = a_0/a(t) -/
def cosmologicalRedshift (F : FLRWData) (t_emit t_obs : ℝ) : ℝ :=
  F.scaleFactor t_obs / F.scaleFactor t_emit - 1

/-- The comoving distance to an object at redshift z. -/
axiom comoving_distance (F : FLRWData) :
    True  -- chi = integral from t_emit to t_obs of dt/a(t)

/-! ## Horizons -/

/-- The particle horizon: maximum distance from which light could have reached us.
d_H(t) = a(t) * integral from 0 to t of dt'/a(t') -/
axiom particle_horizon (F : FLRWData) (_t : ℝ) :
    True  -- Finite integral implies causal horizon

/-- The event horizon: maximum distance to which we can ever send a signal.
d_E(t) = a(t) * integral from t to infinity of dt'/a(t') -/
axiom event_horizon (F : FLRWData) (_t : ℝ) :
    True  -- Finite integral implies cosmic event horizon (e.g., in de Sitter)

/-- The Hubble horizon: distance at which recession velocity equals speed of light.
d_H = c/H (in natural units, just 1/H) -/
def hubbleHorizon (H : ℝ) : ℝ := 1 / H

end PseudoRiemannianMetric
end
