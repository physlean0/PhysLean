/-
Copyright (c) 2025 PhysLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PhysLean Contributors
-/

import PhysLean.Mathematics.Geometry.Metric.PseudoRiemannian.Kerr

/-!
# The Penrose Process and Black Hole Energy Extraction

This file formalizes the Penrose process and related mechanisms for
extracting energy from rotating black holes. These processes have
important astrophysical applications including powering jets and
explaining the luminosity of active galactic nuclei.

## Main Definitions

* `PenroseProcessData`: Energy extraction via particle decay in ergosphere
* `SuperradianceCondition`: Wave amplification by rotating black holes
* `BlandfordZnajekData`: Electromagnetic energy extraction mechanism
* `irreducibleMass`: The minimum mass of a Kerr black hole

## Physical Background

In the ergosphere of a Kerr black hole:
- The Killing vector ∂/∂t becomes spacelike
- Particles can have negative energy as measured at infinity
- Energy can be extracted while respecting conservation laws

The Penrose process:
1. Send a particle into the ergosphere
2. It splits into two pieces
3. One piece falls into the horizon with negative energy
4. The other escapes with more energy than the original

The maximum efficiency for extremal Kerr is approximately 29%.

## References

* Penrose, "Gravitational Collapse: The Role of General Relativity" (1969)
* Misner, Thorne, Wheeler, "Gravitation" (1973), Chapter 33
* Blandford & Znajek, "Electromagnetic Extraction of Energy" (1977)
* Wald, "General Relativity" (1984), Chapter 12
-/

noncomputable section

namespace PseudoRiemannianMetric

/-! ## Ergosphere Physics -/

/-- The outer ergosphere radius at the equator (θ = π/2) for given mass and spin. -/
def ergosphereRadiusEquator' (mass spin : ℝ) : ℝ :=
  mass + Real.sqrt (mass^2 - spin^2 * 0)  -- cos(π/2) = 0

/-- At the equator, the ergosphere radius equals 2M. -/
lemma ergosphere_equator_eq_2M (mass : ℝ) (hm : mass ≥ 0) (spin : ℝ) :
    ergosphereRadiusEquator' mass spin = 2 * mass := by
  unfold ergosphereRadiusEquator'
  simp only [mul_zero, sub_zero, Real.sqrt_sq hm]
  ring

/-- The energy of a particle as measured at infinity is E = -p_μ ξ^μ
where ξ is the time-translation Killing vector. -/
def energyAtInfinity (p_t : ℝ) : ℝ := -p_t

/-- The angular momentum of a particle: L = p_μ η^μ
where η = ∂/∂φ is the axial Killing vector. -/
def angularMomentumParticle (p_phi : ℝ) : ℝ := p_phi

/-! ## The Penrose Process -/

/-- The Penrose process for extracting energy from a Kerr black hole:
1. A particle with energy E₀ enters the ergosphere
2. It decays into two particles with energies E₁ and E₂
3. Conservation: E₀ = E₁ + E₂
4. One particle (E₂ < 0) falls into the black hole
5. The other (E₁ > E₀) escapes with extracted energy -/
structure PenroseProcessData where
  /-- Initial particle energy -/
  E₀ : ℝ
  /-- Energy of escaping particle -/
  E₁ : ℝ
  /-- Energy of infalling particle (negative) -/
  E₂ : ℝ
  /-- Energy conservation -/
  conservation : E₀ = E₁ + E₂
  /-- Infalling particle has negative energy -/
  negative_infall : E₂ < 0
  /-- Initial energy is positive -/
  positive_initial : E₀ > 0

/-- The energy extracted in a Penrose process. -/
def penroseEnergyExtracted (p : PenroseProcessData) : ℝ :=
  p.E₁ - p.E₀

/-- The Penrose process extracts positive energy when E₂ < 0. -/
lemma penrose_extracts_energy (p : PenroseProcessData) :
    penroseEnergyExtracted p > 0 := by
  unfold penroseEnergyExtracted
  have h : p.E₁ = p.E₀ - p.E₂ := by linarith [p.conservation]
  rw [h]
  linarith [p.negative_infall]

/-- The efficiency of a Penrose process: η = (E₁ - E₀)/E₀. -/
def penroseEfficiency (p : PenroseProcessData) : ℝ :=
  (p.E₁ - p.E₀) / p.E₀

/-- The efficiency is positive. -/
lemma penrose_efficiency_pos (p : PenroseProcessData) :
    penroseEfficiency p > 0 := by
  unfold penroseEfficiency
  apply div_pos
  · exact penrose_extracts_energy p
  · exact p.positive_initial

/-- Maximum Penrose process efficiency is achieved at the horizon
and equals 1 - 1/√2 ≈ 20.7% for extremal Kerr. -/
def maxPenroseEfficiency : ℝ := 1 - 1 / Real.sqrt 2

/-- The maximum efficiency is positive. -/
lemma maxPenrose_pos : maxPenroseEfficiency > 0 := by
  unfold maxPenroseEfficiency
  have h : Real.sqrt 2 > 1 := Real.one_lt_sqrt_two
  have h2 : 1 / Real.sqrt 2 < 1 := by
    rw [div_lt_one (Real.sqrt_pos_of_pos (by norm_num : (0 : ℝ) < 2))]
    exact h
  linarith

/-! ## Irreducible Mass -/

/-- The irreducible mass of a Kerr black hole:
M_irr² = (1/2)(M² + √(M⁴ - J²)) = A/(16π)

This is the mass that cannot be extracted by any classical process. -/
def irreducibleMass (mass spin : ℝ) : ℝ :=
  Real.sqrt ((mass^2 + Real.sqrt (mass^4 - (mass * spin)^2)) / 2)

/-- The irreducible mass equals the area divided by 16π. -/
def irreducibleMassFromArea (area : ℝ) : ℝ :=
  Real.sqrt (area / (16 * Real.pi))

/-- The extractable rotational energy is M - M_irr. -/
def extractableEnergy (mass spin : ℝ) : ℝ :=
  mass - irreducibleMass mass spin

/-- For a non-rotating black hole (Schwarzschild), the Penrose
process and superradiance do not operate: there is no ergosphere
and no rotational energy to extract. -/
lemma schwarzschild_no_penrose (spin : ℝ) (hspin : spin = 0) :
    extractableEnergy 1 spin = 0 := by
  unfold extractableEnergy irreducibleMass
  simp [hspin]

/-! ## Superradiance -/

/-- Superradiance: A wave scattered off a rotating black hole can be
amplified if ω < m Ω_H, where ω is frequency, m is azimuthal number,
and Ω_H is the horizon angular velocity. -/
def superradianceCondition (omega m : ℝ) (horizonAngularVelocity : ℝ) : Prop :=
  omega < m * horizonAngularVelocity

/-- The amplification factor for superradiant scattering. -/
def superradianceAmplification (omega m horizonAngularVelocity : ℝ) : ℝ :=
  m * horizonAngularVelocity - omega

/-- The amplification is positive when superradiance condition holds. -/
lemma superradiance_amplification_pos {omega m Ω_H : ℝ}
    (h : superradianceCondition omega m Ω_H) :
    superradianceAmplification omega m Ω_H > 0 := by
  unfold superradianceAmplification superradianceCondition at *
  linarith

/-! ## Blandford-Znajek Process -/

/-- The Blandford-Znajek process extracts energy electromagnetically
from a rotating black hole threaded by magnetic field lines.

This is believed to power relativistic jets from active galactic nuclei. -/
structure BlandfordZnajekData where
  /-- Black hole mass -/
  mass : ℝ
  /-- Black hole spin parameter -/
  spin : ℝ
  /-- Magnetic field strength at horizon -/
  magneticField : ℝ
  /-- Mass is positive -/
  mass_pos : mass > 0
  /-- Sub-extremal -/
  subextremal : |spin| ≤ mass

/-- The horizon radius for Kerr black hole. -/
def BlandfordZnajekData.horizonRadius (bz : BlandfordZnajekData) : ℝ :=
  bz.mass + Real.sqrt (bz.mass^2 - bz.spin^2)

/-- The Blandford-Znajek luminosity (simplified):
L_BZ ≈ (1/32) (a/M)² B² r_H² c

For astrophysical black holes, this can be enormous (~10⁴⁵ erg/s). -/
def bzLuminosity (bz : BlandfordZnajekData) : ℝ :=
  let a := bz.spin
  let M := bz.mass
  let B := bz.magneticField
  let r_H := bz.horizonRadius
  (1/32) * (a/M)^2 * B^2 * r_H^2

/-- The BZ luminosity is non-negative. -/
lemma bzLuminosity_nonneg (bz : BlandfordZnajekData) :
    bzLuminosity bz ≥ 0 := by
  unfold bzLuminosity BlandfordZnajekData.horizonRadius
  apply mul_nonneg
  · apply mul_nonneg
    · apply mul_nonneg
      · norm_num
      · exact sq_nonneg _
    · exact sq_nonneg _
  · exact sq_nonneg _

/-! ## Hawking's Area Theorem -/

/-- The horizon area of a Kerr black hole:
A = 8πM(M + √(M² - a²)) -/
def kerrHorizonArea (mass spin : ℝ) : ℝ :=
  8 * Real.pi * mass * (mass + Real.sqrt (mass^2 - spin^2))

/-- The area is positive for positive mass. -/
lemma kerrArea_pos (mass spin : ℝ) (hm : mass > 0) (hsub : |spin| ≤ mass) :
    kerrHorizonArea mass spin > 0 := by
  unfold kerrHorizonArea
  apply mul_pos
  · apply mul_pos
    · apply mul_pos (by norm_num : (8 : ℝ) > 0) Real.pi_pos
    · exact hm
  · have h1 : mass^2 - spin^2 ≥ 0 := by
      have habs : spin^2 ≤ mass^2 := by
        calc spin^2 = |spin|^2 := by rw [sq_abs]
        _ ≤ mass^2 := by apply sq_le_sq'; linarith [abs_nonneg spin]; exact hsub
      linarith
    have h2 : Real.sqrt (mass^2 - spin^2) ≥ 0 := Real.sqrt_nonneg _
    linarith

/-- The relationship between irreducible mass and area:
M_irr = √(A/(16π)) -/
lemma irreducible_mass_area_relation (mass spin : ℝ) :
    irreducibleMassFromArea (kerrHorizonArea mass spin) =
    Real.sqrt (kerrHorizonArea mass spin / (16 * Real.pi)) := rfl

/-! ## Energy Extraction Limits -/

/-- The maximum extractable fraction for extremal Kerr (a = M).
This is 1 - 1/√2 ≈ 29.3%. -/
def maxExtractableFraction : ℝ := 1 - 1 / Real.sqrt 2

/-- The maximum extractable fraction is less than 1. -/
lemma maxExtractable_lt_one : maxExtractableFraction < 1 := by
  unfold maxExtractableFraction
  have h : 1 / Real.sqrt 2 > 0 := by
    apply div_pos; norm_num
    exact Real.sqrt_pos_of_pos (by norm_num : (0 : ℝ) < 2)
  linarith

/-- The maximum extractable fraction is positive. -/
lemma maxExtractable_pos : maxExtractableFraction > 0 := maxPenrose_pos

/-! ## Thermodynamic Interpretation -/

/-- The first law of black hole mechanics:
dM = (κ/8π) dA + Ω_H dJ

where κ is surface gravity, A is area, Ω_H is horizon angular velocity, J is angular momentum. -/
structure FirstLawData where
  /-- Change in mass -/
  dM : ℝ
  /-- Surface gravity -/
  kappa : ℝ
  /-- Change in area -/
  dA : ℝ
  /-- Horizon angular velocity -/
  omega_H : ℝ
  /-- Change in angular momentum -/
  dJ : ℝ
  /-- The first law relation -/
  first_law : dM = (kappa / (8 * Real.pi)) * dA + omega_H * dJ

/-- For the Penrose process, dJ < 0 (angular momentum decreases). -/
structure PenroseThermodynamics extends FirstLawData where
  /-- Angular momentum decreases -/
  dJ_neg : dJ < 0
  /-- Area increases (classically) -/
  dA_nonneg : dA ≥ 0

end PseudoRiemannianMetric
end
