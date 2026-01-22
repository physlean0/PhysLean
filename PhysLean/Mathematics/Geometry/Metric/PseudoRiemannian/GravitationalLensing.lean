/-
Copyright (c) 2025 PhysLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PhysLean Contributors
-/

import PhysLean.Mathematics.Geometry.Metric.PseudoRiemannian.Schwarzschild
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Gravitational Lensing

This file formalizes gravitational lensing effects in general relativity,
where light rays are bent by gravitational fields.

## Main Definitions

* `deflectionAngleSchwarzschild`: The angle by which light is bent by a mass
* `einsteinRadius`: The characteristic angular scale for lensing
* `shapiroDelay`: The time delay of signals passing near a massive object
* `LensingGeometry`: The lens-source-observer configuration

## Physical Background

Gravitational lensing is caused by:
- Curved spacetime near massive objects
- Light following null geodesics (shortest paths in spacetime)
- Multiple images, magnification, and distortion of sources

Key phenomena:
- Light deflection by the Sun (1.75 arcsec) - confirmed 1919
- Shapiro time delay - confirmed by radar to planets
- Einstein rings and arcs from galaxies/clusters
- Gravitational microlensing from stars

## References

* Misner, Thorne, Wheeler, "Gravitation" (1973), Chapters 25, 40
* Schneider, Ehlers, Falco, "Gravitational Lenses" (1992)
* Wald, "General Relativity" (1984), Chapter 6
-/

noncomputable section

namespace PseudoRiemannianMetric

/-! ## Light Deflection -/

/-- The deflection angle for light passing a point mass M at impact parameter b.
In GR: Δφ = 4GM/(c²b) = 2r_s/b (in geometric units)

This is twice the Newtonian prediction, famously confirmed in 1919. -/
def deflectionAngleSchwarzschild (mass : ℝ) (impactParameter : ℝ) : ℝ :=
  4 * mass / impactParameter

/-- The deflection angle is positive for positive mass and impact parameter. -/
lemma lightDeflection_pos (mass b : ℝ) (hm : mass > 0) (hb : b > 0) :
    deflectionAngleSchwarzschild mass b > 0 := by
  unfold deflectionAngleSchwarzschild
  positivity

/-- Light deflection in the weak-field limit: the angle is proportional to M/b. -/
lemma deflection_angle_proportional (mass b : ℝ) (_hb : b > 0) (c : ℝ) (hc : c > 0) :
    deflectionAngleSchwarzschild mass (c * b) =
    deflectionAngleSchwarzschild mass b / c := by
  unfold deflectionAngleSchwarzschild
  have hc_ne : c ≠ 0 := ne_of_gt hc
  field_simp

/-- Deflection scales inversely with impact parameter. -/
lemma deflection_scaling (mass b₁ b₂ : ℝ) (hb₁ : b₁ > 0) (hb₂ : b₂ > 0) :
    deflectionAngleSchwarzschild mass b₁ * b₁ =
    deflectionAngleSchwarzschild mass b₂ * b₂ := by
  unfold deflectionAngleSchwarzschild
  have hb₁_ne : b₁ ≠ 0 := ne_of_gt hb₁
  have hb₂_ne : b₂ ≠ 0 := ne_of_gt hb₂
  field_simp

/-! ## Lensing Geometry -/

/-- The geometry of a gravitational lensing system: source, lens, and observer. -/
structure LensingGeometry where
  /-- Distance from observer to lens -/
  D_L : ℝ
  /-- Distance from observer to source -/
  D_S : ℝ
  /-- Distance from lens to source -/
  D_LS : ℝ
  /-- Mass of the lens -/
  lensMass : ℝ
  /-- Angular position of the source (unlensed) -/
  β : ℝ
  /-- All distances are positive -/
  D_L_pos : D_L > 0
  D_S_pos : D_S > 0
  D_LS_pos : D_LS > 0
  /-- Mass is positive -/
  mass_pos : lensMass > 0

/-- The Einstein radius: the characteristic angular scale for strong lensing.
θ_E = √(4GM D_LS / (c² D_L D_S)) -/
def einsteinRadius (geom : LensingGeometry) : ℝ :=
  Real.sqrt (4 * geom.lensMass * geom.D_LS / (geom.D_L * geom.D_S))

/-- The Einstein radius is positive. -/
lemma einsteinRadius_pos (geom : LensingGeometry) : einsteinRadius geom > 0 := by
  unfold einsteinRadius
  apply Real.sqrt_pos_of_pos
  apply div_pos
  · apply mul_pos
    · apply mul_pos; norm_num; exact geom.mass_pos
    · exact geom.D_LS_pos
  · exact mul_pos geom.D_L_pos geom.D_S_pos

/-- The Einstein radius in physical units at the lens plane. -/
def einsteinRadiusPhysical (geom : LensingGeometry) : ℝ :=
  einsteinRadius geom * geom.D_L

/-- The physical Einstein radius is positive. -/
lemma einsteinRadiusPhysical_pos (geom : LensingGeometry) :
    einsteinRadiusPhysical geom > 0 := by
  unfold einsteinRadiusPhysical
  exact mul_pos (einsteinRadius_pos geom) geom.D_L_pos

/-! ## Lens Equation -/

/-- The lens equation relates observed position θ to source position β:
β = θ - α(θ)
where α is the deflection angle.

For a point mass: β = θ - θ_E²/θ -/
def lensEquationPointMass (geom : LensingGeometry) (θ : ℝ) : ℝ :=
  let θ_E := einsteinRadius geom
  θ - θ_E^2 / θ

/-- Image positions for a point mass lens:
θ_± = (β ± √(β² + 4θ_E²)) / 2 -/
def imagePositions (geom : LensingGeometry) : ℝ × ℝ :=
  let θ_E := einsteinRadius geom
  let discriminant := geom.β^2 + 4 * θ_E^2
  ((geom.β + Real.sqrt discriminant) / 2,
   (geom.β - Real.sqrt discriminant) / 2)

/-- The discriminant for image positions is always positive. -/
lemma imagePositions_discriminant_pos (geom : LensingGeometry) :
    geom.β^2 + 4 * (einsteinRadius geom)^2 > 0 := by
  have h1 : geom.β^2 ≥ 0 := sq_nonneg _
  have h2 : (einsteinRadius geom)^2 > 0 := sq_pos_of_pos (einsteinRadius_pos geom)
  linarith

/-! ## Einstein Ring -/

/-- An Einstein ring forms when source, lens, and observer are perfectly aligned (β = 0).
The ring has angular radius θ_E. -/
def isEinsteinRing (geom : LensingGeometry) : Prop :=
  geom.β = 0

/-- For an Einstein ring, both image positions have magnitude θ_E. -/
lemma einstein_ring_positions (geom : LensingGeometry) (hRing : isEinsteinRing geom) :
    let (θ_plus, θ_minus) := imagePositions geom
    θ_plus = einsteinRadius geom ∧ θ_minus = -(einsteinRadius geom) := by
  unfold imagePositions isEinsteinRing at *
  simp only [hRing, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_add]
  have h1 : Real.sqrt (4 * (einsteinRadius geom)^2) = 2 * einsteinRadius geom := by
    rw [Real.sqrt_eq_iff_eq_sq]
    · ring
    · apply mul_nonneg; norm_num; exact sq_nonneg _
    · linarith [einsteinRadius_pos geom]
  simp only [h1]
  constructor
  · ring
  · ring

/-! ## Magnification -/

/-- The magnification of an image for a point mass lens.
μ = |θ/(θ² - θ_E²)| × |d(θ² - θ_E²)/dθ| -/
def magnificationPointMass (geom : LensingGeometry) (θ : ℝ) : ℝ :=
  let θ_E := einsteinRadius geom
  let u := θ^2 - θ_E^2
  if u ≠ 0 then θ^2 / |u| else 0

/-- The total magnification formula for a point mass:
μ_total = (u² + 2) / (u √(u² + 4)) where u = β/θ_E -/
def totalMagnificationFormula (geom : LensingGeometry) : ℝ :=
  let θ_E := einsteinRadius geom
  let u := geom.β / θ_E
  (u^2 + 2) / (u * Real.sqrt (u^2 + 4))

/-! ## Shapiro Time Delay -/

/-- The Shapiro time delay: light signals are delayed when passing near massive objects.

Δt = (4GM/c³) ln((r₁ + x₁)(r₂ + x₂) / b²) -/
def shapiroDelay (mass r₁ r₂ b : ℝ) : ℝ :=
  4 * mass * Real.log ((r₁ + r₂)^2 / b^2)

/-- For a radar signal to a planet, the delay formula. -/
def shapiroDelayRadar (mass r_earth r_planet b : ℝ) : ℝ :=
  4 * mass * Real.log (4 * r_earth * r_planet / b^2)

/-- The Shapiro delay is positive when the argument of log is > 1. -/
lemma shapiroDelay_pos (mass r₁ r₂ b : ℝ) (hm : mass > 0)
    (h : (r₁ + r₂)^2 / b^2 > 1) :
    shapiroDelay mass r₁ r₂ b > 0 := by
  unfold shapiroDelay
  apply mul_pos
  · linarith
  · exact Real.log_pos h

/-! ## Gravitational Redshift -/

/-- Gravitational redshift: photons lose energy climbing out of a gravitational well.
z = Δλ/λ = Δν/ν ≈ GM/(c²r) for weak fields. -/
def gravitationalRedshiftWeak (mass r : ℝ) : ℝ :=
  mass / r

/-- The weak-field redshift is positive. -/
lemma gravitationalRedshiftWeak_pos (mass r : ℝ) (hm : mass > 0) (hr : r > 0) :
    gravitationalRedshiftWeak mass r > 0 := by
  unfold gravitationalRedshiftWeak
  exact div_pos hm hr

/-- For Schwarzschild, the exact redshift factor is:
1 + z = 1/√(1 - r_s/r) -/
def gravitationalRedshiftSchwarzschild (mass r : ℝ) : ℝ :=
  1 / Real.sqrt (1 - 2 * mass / r) - 1

/-! ## Microlensing -/

/-- Gravitational microlensing occurs when the lens is a stellar-mass object
and the images cannot be resolved, but magnification varies over time. -/
structure MicrolensingEvent where
  /-- Mass of the lensing object -/
  lensMass : ℝ
  /-- Relative transverse velocity -/
  velocity : ℝ
  /-- Minimum impact parameter -/
  u₀ : ℝ
  /-- Time of closest approach -/
  t₀ : ℝ
  /-- Einstein radius crossing time -/
  t_E : ℝ
  /-- Mass is positive -/
  mass_pos : lensMass > 0
  /-- Crossing time is positive -/
  t_E_pos : t_E > 0

/-- The impact parameter as a function of time during a microlensing event.
u(t) = √(u₀² + ((t-t₀)/t_E)²) -/
def microlensingImpactParameter (event : MicrolensingEvent) (t : ℝ) : ℝ :=
  Real.sqrt (event.u₀^2 + ((t - event.t₀) / event.t_E)^2)

/-- The magnification as a function of time during a microlensing event.
μ(t) = (u² + 2) / (u√(u² + 4)) -/
def microlensingMagnification (event : MicrolensingEvent) (t : ℝ) : ℝ :=
  let u := microlensingImpactParameter event t
  (u^2 + 2) / (u * Real.sqrt (u^2 + 4))

/-- The characteristic microlensing light curve is symmetric about t₀. -/
lemma microlensing_symmetric (event : MicrolensingEvent) (t : ℝ) :
    microlensingMagnification event (event.t₀ + t) =
    microlensingMagnification event (event.t₀ - t) := by
  unfold microlensingMagnification microlensingImpactParameter
  have h1 : event.t₀ + t - event.t₀ = t := by ring
  have h2 : event.t₀ - t - event.t₀ = -t := by ring
  simp only [h1, h2]
  have h3 : (t / event.t_E)^2 = (-t / event.t_E)^2 := by ring
  rw [h3]

/-! ## Strong and Weak Lensing -/

/-- Strong lensing produces multiple resolved images, arcs, or Einstein rings.
This occurs when the source is within about 2θ_E of the optical axis. -/
def isStrongLensing (geom : LensingGeometry) : Prop :=
  |geom.β| < 2 * einsteinRadius geom

/-- Weak lensing produces small distortions (shear) of background galaxies. -/
def isWeakLensing (geom : LensingGeometry) : Prop :=
  |geom.β| > 2 * einsteinRadius geom

/-- The critical curve for axisymmetric lenses is at the Einstein radius. -/
def criticalCurve (geom : LensingGeometry) : ℝ := einsteinRadius geom

/-- The caustic for a point mass is a single point at the origin. -/
def causticPointMass : ℝ := 0

end PseudoRiemannianMetric
end
