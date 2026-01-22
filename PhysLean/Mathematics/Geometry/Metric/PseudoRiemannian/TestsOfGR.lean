/-
Copyright (c) 2025 PhysLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PhysLean Contributors
-/

import PhysLean.Mathematics.Geometry.Metric.PseudoRiemannian.Schwarzschild
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Classical and Modern Tests of General Relativity

This file formalizes the experimental tests of general relativity, from the
classical tests proposed by Einstein to modern high-precision measurements.

## Main Definitions

* `OrbitalData`: Parameters for a Keplerian orbit
* `perihelionPrecessionPerOrbit`: GR perihelion precession formula
* `lightDeflectionAngle`: Light bending by massive objects
* `gravitationalRedshiftPotential`: Frequency shift in gravitational fields
* `shapiroDelayFormula`: Time delay of signals passing near masses

## Historical Context

Einstein proposed three classical tests in 1915-1916:
1. Perihelion precession of Mercury (known anomaly, explained by GR)
2. Light deflection by the Sun (predicted, confirmed 1919)
3. Gravitational redshift (predicted, confirmed 1959)

The fourth classical test was added later:
4. Shapiro time delay (predicted 1964, confirmed 1968)

Modern tests include:
- Binary pulsar observations (gravitational waves indirectly)
- Gravitational wave detection (LIGO 2015)
- Frame dragging (Gravity Probe B)
- Strong-field tests (black hole shadows, gravitational wave ringdown)

## Experimental Confirmations

All tests of general relativity are consistent with the theory:
- Mercury precession: 42.98 ± 0.04 arcsec/century (GR predicts 42.98)
- Light deflection: 1.75 arcsec at solar limb (confirmed 1919, VLBI to 0.01%)
- Gravitational redshift: Pound-Rebka (1959), GPS corrections
- Shapiro delay: Cassini |γ-1| < 2.3×10⁻⁵
- Binary pulsars: Period decay matches GR to 0.2%
- Gravitational waves: LIGO GW150914 (2015)

## References

* Misner, Thorne, Wheeler, "Gravitation" (1973), Chapters 38-40
* Will, "Theory and Experiment in Gravitational Physics" (2018)
* Will, "The Confrontation between GR and Experiment" (Living Reviews, 2014)
-/

noncomputable section

namespace PseudoRiemannianMetric

/-! ## Test 1: Perihelion Precession -/

/-- Data for a Keplerian orbit in a gravitational field. -/
structure OrbitalData where
  /-- Semi-major axis a -/
  semiMajorAxis : ℝ
  /-- Eccentricity e (0 ≤ e < 1 for ellipse) -/
  eccentricity : ℝ
  /-- Mass of central body M -/
  centralMass : ℝ
  /-- Orbital period T -/
  period : ℝ
  /-- Semi-major axis is positive -/
  a_pos : semiMajorAxis > 0
  /-- Eccentricity is in valid range -/
  e_range : 0 ≤ eccentricity ∧ eccentricity < 1

/-- The general relativistic perihelion precession per orbit:
Δω = 6πGM / (c²a(1-e²))

This arises from the 1/r³ correction to the Newtonian potential in the
Schwarzschild geometry. In geometric units (G = c = 1). -/
def perihelionPrecessionPerOrbit (orbit : OrbitalData) : ℝ :=
  6 * Real.pi * orbit.centralMass /
    (orbit.semiMajorAxis * (1 - orbit.eccentricity^2))

/-- The perihelion precession rate (radians per unit time). -/
def perihelionPrecessionRate (orbit : OrbitalData) : ℝ :=
  perihelionPrecessionPerOrbit orbit / orbit.period

/-- The precession is positive for positive mass. -/
lemma precession_pos (orbit : OrbitalData) (hm : orbit.centralMass > 0) :
    perihelionPrecessionPerOrbit orbit > 0 := by
  unfold perihelionPrecessionPerOrbit
  apply div_pos
  · apply mul_pos
    · apply mul_pos (by norm_num : (6 : ℝ) > 0) Real.pi_pos
    · exact hm
  · apply mul_pos orbit.a_pos
    have he := orbit.e_range
    have h : orbit.eccentricity^2 < 1 := by nlinarith
    linarith

/-- The precession increases for smaller orbits. -/
lemma precession_scaling (mass ecc a c : ℝ) (hc : c > 0) (ha : a > 0)
    (he : 0 ≤ ecc ∧ ecc < 1) :
    let prec := fun semi => 6 * Real.pi * mass / (semi * (1 - ecc^2))
    prec (c * a) = prec a / c := by
  simp only
  have hc_ne : c ≠ 0 := ne_of_gt hc
  have ha_ne : a ≠ 0 := ne_of_gt ha
  field_simp

/-! ## Test 2: Light Deflection -/

/-- The deflection angle for light passing at impact parameter b from a mass M:
Δθ = 4GM / (c²b)

This is twice the Newtonian prediction. In geometric units (G = c = 1). -/
def lightDeflectionAngle (mass impactParameter : ℝ) : ℝ :=
  4 * mass / impactParameter

/-- The deflection is positive for positive mass and impact parameter. -/
lemma deflection_pos (mass b : ℝ) (hm : mass > 0) (hb : b > 0) :
    lightDeflectionAngle mass b > 0 := by
  unfold lightDeflectionAngle
  positivity

/-- The factor of 2 between GR and Newtonian predictions. -/
lemma deflection_gr_vs_newtonian (mass b : ℝ) :
    lightDeflectionAngle mass b = 2 * (2 * mass / b) := by
  unfold lightDeflectionAngle
  ring

/-! ## Test 3: Gravitational Redshift -/

/-- The gravitational redshift between two points at different gravitational potentials:
z = Δν/ν = ΔΦ/c² = GM/c² × (1/r₁ - 1/r₂)

Photons climbing out of a gravitational well lose energy. In geometric units. -/
def gravitationalRedshiftPotential (mass r1 r2 : ℝ) : ℝ :=
  mass * (1/r1 - 1/r2)

/-- For emission at r₁ received at r₂ > r₁, redshift is positive. -/
lemma redshift_positive (mass r1 r2 : ℝ) (hm : mass > 0) (hr : r2 > r1) (hr1 : r1 > 0) :
    gravitationalRedshiftPotential mass r1 r2 > 0 := by
  unfold gravitationalRedshiftPotential
  have h1 : 1/r1 > 1/r2 := by
    apply one_div_lt_one_div_of_lt
    · linarith
    · exact hr
  have h2 : 1/r1 - 1/r2 > 0 := by linarith
  nlinarith

/-- Redshift scales linearly with mass. -/
lemma redshift_mass_scaling (mass r1 r2 c : ℝ) :
    gravitationalRedshiftPotential (c * mass) r1 r2 =
    c * gravitationalRedshiftPotential mass r1 r2 := by
  unfold gravitationalRedshiftPotential
  ring

/-! ## Test 4: Shapiro Time Delay -/

/-- The Shapiro time delay for a signal passing near a massive object:
Δt = 4GM/c³ × [1 + ln(4r₁r₂/b²)]

Signals are delayed when passing through curved spacetime. In geometric units. -/
def shapiroDelayFormula (mass r1 r2 b : ℝ) : ℝ :=
  4 * mass * (1 + Real.log (4 * r1 * r2 / b^2))

/-- The maximum delay occurs at superior conjunction. -/
def shapiroDelayMaximum (mass r_earth r_planet r_sun : ℝ) : ℝ :=
  shapiroDelayFormula mass r_earth r_planet r_sun

/-! ## Binary Pulsar Tests -/

/-- Data for a binary pulsar system. -/
structure BinaryPulsarData where
  /-- Masses of the two neutron stars -/
  mass1 : ℝ
  mass2 : ℝ
  /-- Orbital period -/
  orbitalPeriod : ℝ
  /-- Orbital eccentricity -/
  eccentricity : ℝ
  /-- Rate of period decay dP/dt -/
  periodDerivative : ℝ

/-- The orbital period decay from gravitational wave emission (simplified). -/
def binaryPulsarPeriodDecay (pulsar : BinaryPulsarData) : ℝ :=
  -(192 * Real.pi / 5) * pulsar.eccentricity

/-! ## Frame Dragging -/

/-- The Lense-Thirring precession rate for frame dragging by a rotating mass. -/
def lenseThirringRate (angularMomentum r : ℝ) : ℝ :=
  angularMomentum / r^3

/-- Frame dragging rate is positive for positive angular momentum and radius. -/
lemma lenseThirring_pos (J r : ℝ) (hJ : J > 0) (hr : r > 0) :
    lenseThirringRate J r > 0 := by
  unfold lenseThirringRate
  positivity

end PseudoRiemannianMetric
end
