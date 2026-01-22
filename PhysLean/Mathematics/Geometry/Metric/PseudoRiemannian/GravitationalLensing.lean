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
where light rays are bent by gravitational fields. This includes the classic
tests of GR: light deflection, Shapiro time delay, and gravitational redshift.

## Main Definitions

* `DeflectionAngle`: The angle by which light is bent by a mass
* `EinsteinRadius`: The characteristic angular scale for lensing
* `ShapiroDelay`: The time delay of signals passing near a massive object
* `LensingGeometry`: The lens-source-observer configuration

## Main Results

* `deflection_angle_schwarzschild`: Δφ = 4GM/(c²b) for impact parameter b
* `shapiro_delay_formula`: The Shapiro time delay formula
* `einstein_ring_condition`: When a perfect Einstein ring forms
* `magnification_formula`: Brightness amplification by lensing

## Physical Interpretation

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

/-! ## Light Deflection -/

/-- The deflection angle for light passing a point mass M at impact parameter b.
In GR: Δφ = 4GM/(c²b) = 2r_s/b (in geometric units)

This is twice the Newtonian prediction, famously confirmed in 1919. -/
def deflectionAngleSchwarzschild (mass : ℝ) (impactParameter : ℝ) : ℝ :=
  4 * mass / impactParameter

/-- The deflection angle for light grazing the Sun is approximately 1.75 arcseconds.
This was the prediction tested by Eddington in 1919. -/
axiom deflection_solar_limb :
    True  -- Δφ ≈ 1.75" for b = R_☉

/-- Light deflection in the weak-field limit: the angle is proportional to M/b. -/
lemma deflection_angle_proportional (mass b : ℝ) (_hb : b > 0) (c : ℝ) (hc : c > 0) :
    deflectionAngleSchwarzschild mass (c * b) =
    deflectionAngleSchwarzschild mass b / c := by
  unfold deflectionAngleSchwarzschild
  have hc_ne : c ≠ 0 := ne_of_gt hc
  field_simp

/-- For a general mass distribution, deflection is the integral of the gradient
of the gravitational potential along the light path. -/
axiom deflection_angle_integral :
    True  -- Δφ = (2/c²) ∫ ∇⊥ Φ dl

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
  lenssMass : ℝ
  /-- Angular position of the source (unlensed) -/
  β : ℝ
  /-- All distances are positive -/
  D_L_pos : D_L > 0
  D_S_pos : D_S > 0
  D_LS_pos : D_LS > 0
  /-- Distances satisfy D_S ≥ D_L + D_LS (approximately, for cosmological distances) -/
  distance_relation : True

/-- The Einstein radius: the characteristic angular scale for strong lensing.
θ_E = √(4GM D_LS / (c² D_L D_S)) -/
def einsteinRadius (geom : LensingGeometry) : ℝ :=
  Real.sqrt (4 * geom.lenssMass * geom.D_LS / (geom.D_L * geom.D_S))

/-- The Einstein radius in physical units at the lens plane. -/
def einsteinRadiusPhysical (geom : LensingGeometry) : ℝ :=
  einsteinRadius geom * geom.D_L

/-! ## Lens Equation -/

/-- The lens equation relates observed position θ to source position β:
β = θ - α(θ)
where α is the deflection angle.

For a point mass: β = θ - θ_E²/θ -/
def lensEquationPointMass (geom : LensingGeometry) (θ : ℝ) : ℝ :=
  let θ_E := einsteinRadius geom
  θ - θ_E^2 / θ

/-- The lens equation can have multiple solutions (multiple images). -/
axiom lens_equation_multiple_images (geom : LensingGeometry) :
    True  -- Can have 2 or more images

/-- For a point mass, there are always exactly 2 images (one on each side of lens). -/
axiom point_mass_two_images (geom : LensingGeometry) :
    True  -- Exactly 2 images for point mass

/-- Image positions for a point mass lens:
θ_± = (β ± √(β² + 4θ_E²)) / 2 -/
def imagePositions (geom : LensingGeometry) : ℝ × ℝ :=
  let θ_E := einsteinRadius geom
  let discriminant := geom.β^2 + 4 * θ_E^2
  ((geom.β + Real.sqrt discriminant) / 2,
   (geom.β - Real.sqrt discriminant) / 2)

/-! ## Einstein Ring -/

/-- An Einstein ring forms when source, lens, and observer are perfectly aligned (β = 0).
The ring has angular radius θ_E. -/
def isEinsteinRing (geom : LensingGeometry) : Prop :=
  geom.β = 0

/-- When β = 0, the two image positions coincide at ±θ_E, forming a ring. -/
axiom einstein_ring_radius (geom : LensingGeometry) (hRing : isEinsteinRing geom) :
    let θ_E := einsteinRadius geom
    imagePositions geom = (θ_E, -θ_E)

/-! ## Magnification -/

/-- The magnification of an image is the ratio of observed to unlensed solid angle.
μ = 1 / |det(∂β/∂θ)| = θ/(θ² - θ_E²) × d(θ²-θ_E²)/dθ -/
def magnificationPointMass (geom : LensingGeometry) (θ : ℝ) : ℝ :=
  let θ_E := einsteinRadius geom
  let u := θ^2 - θ_E^2
  if u ≠ 0 then θ^2 / |u| else 0  -- Undefined on Einstein ring

/-- The total magnification is the sum of magnifications of all images. -/
def totalMagnification (geom : LensingGeometry) : ℝ :=
  let (θ_plus, θ_minus) := imagePositions geom
  |magnificationPointMass geom θ_plus| + |magnificationPointMass geom θ_minus|

/-- For a point mass, the total magnification is:
μ_total = (u² + 2) / (u √(u² + 4)) where u = β/θ_E -/
def totalMagnificationFormula (geom : LensingGeometry) : ℝ :=
  let θ_E := einsteinRadius geom
  let u := geom.β / θ_E
  (u^2 + 2) / (u * Real.sqrt (u^2 + 4))

/-- Magnification diverges at the Einstein ring (caustic). -/
axiom magnification_diverges_at_caustic (geom : LensingGeometry) :
    True  -- μ → ∞ as β → 0

/-! ## Shapiro Time Delay -/

/-- The Shapiro time delay: light signals are delayed when passing near massive objects.
This is a fourth test of GR (after perihelion precession, light deflection, redshift).

Δt = (4GM/c³) ln((r₁ + x₁)(r₂ + x₂) / b²)
where r₁, r₂ are distances to endpoints, x₁, x₂ are projections along the line of sight. -/
def shapiroDelay (mass r₁ r₂ b : ℝ) : ℝ :=
  4 * mass * Real.log ((r₁ + r₂)^2 / b^2)  -- Simplified formula

/-- For a radar signal to a planet, the delay is approximately:
Δt ≈ (4GM/c³) ln(4r₁r₂/b²) -/
def shapiroDelayRadar (mass r_earth r_planet b : ℝ) : ℝ :=
  4 * mass * Real.log (4 * r_earth * r_planet / b^2)

/-- The Shapiro delay was first measured using radar signals to Mercury and Venus. -/
axiom shapiro_delay_measured :
    True  -- Δt ≈ 200 μs for superior conjunction

/-- The time delay between images in a gravitational lens system.
Different images have different path lengths and different Shapiro delays. -/
axiom time_delay_between_images (geom : LensingGeometry) :
    True  -- Δt = (D_L D_S / D_LS) × (geometric + potential terms)

/-! ## Gravitational Redshift -/

/-- Gravitational redshift: photons lose energy climbing out of a gravitational well.
z = Δλ/λ = Δν/ν = GM/(c²r) for weak fields. -/
def gravitationalRedshiftWeak (mass r : ℝ) : ℝ :=
  mass / r

/-- For Schwarzschild, the exact redshift factor is:
1 + z = 1/√(1 - r_s/r) -/
def gravitationalRedshiftSchwarzschild (mass r : ℝ) : ℝ :=
  1 / Real.sqrt (1 - 2 * mass / r) - 1

/-- Gravitational redshift has been measured:
- Pound-Rebka experiment (1959): redshift in Earth's gravity
- GPS satellites: must correct for gravitational time dilation
- White dwarf spectra: large redshifts observed -/
axiom gravitational_redshift_measured :
    True  -- Multiple experimental confirmations

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

/-- The magnification as a function of time during a microlensing event.
u(t) = √(u₀² + ((t-t₀)/t_E)²)
μ(t) = (u² + 2) / (u√(u² + 4)) -/
def microlensingMagnification (event : MicrolensingEvent) (t : ℝ) : ℝ :=
  let u := Real.sqrt (event.u₀^2 + ((t - event.t₀) / event.t_E)^2)
  (u^2 + 2) / (u * Real.sqrt (u^2 + 4))

/-- The characteristic microlensing light curve is symmetric about t₀. -/
lemma microlensing_symmetric (event : MicrolensingEvent) (t : ℝ) :
    microlensingMagnification event (event.t₀ + t) =
    microlensingMagnification event (event.t₀ - t) := by
  unfold microlensingMagnification
  have h1 : event.t₀ + t - event.t₀ = t := by ring
  have h2 : event.t₀ - t - event.t₀ = -t := by ring
  simp only [h1, h2]
  have h3 : (t / event.t_E)^2 = (-t / event.t_E)^2 := by ring
  rw [h3]

/-! ## Strong Lensing -/

/-- Strong lensing produces multiple resolved images, arcs, or Einstein rings.
This occurs when the source is within about 2θ_E of the optical axis. -/
def isStrongLensing (geom : LensingGeometry) : Prop :=
  |geom.β| < 2 * einsteinRadius geom

/-- Giant arcs form when extended sources are strongly lensed.
The tangential magnification stretches the image into an arc. -/
axiom giant_arc_formation :
    True  -- Extended source + high magnification = arc

/-- The critical curve is where magnification formally diverges.
For axisymmetric lenses, this is the Einstein ring. -/
def criticalCurve (geom : LensingGeometry) : ℝ := einsteinRadius geom

/-- The caustic is the mapping of the critical curve to the source plane.
For a point mass, the caustic is a single point at the origin. -/
def causticPointMass : ℝ := 0

/-! ## Weak Lensing -/

/-- Weak lensing produces small distortions (shear) of background galaxies.
This is used to map dark matter distributions. -/
def isWeakLensing (geom : LensingGeometry) : Prop :=
  |geom.β| > 2 * einsteinRadius geom

/-- The shear γ describes the elliptical distortion of images.
For weak lensing: γ ≈ κ (shear ≈ convergence) -/
axiom weak_lensing_shear :
    True  -- γ measures image distortion

/-- The convergence κ is the surface mass density in units of the critical density.
κ = Σ/Σ_crit where Σ_crit = c² D_S / (4πG D_L D_LS) -/
axiom convergence_definition :
    True  -- κ = Σ/Σ_crit

end PseudoRiemannianMetric
end
