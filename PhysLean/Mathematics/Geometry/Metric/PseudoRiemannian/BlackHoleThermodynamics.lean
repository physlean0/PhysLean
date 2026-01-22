/-
Copyright (c) 2025 PhysLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PhysLean Contributors
-/

import PhysLean.Mathematics.Geometry.Metric.PseudoRiemannian.Schwarzschild

/-!
# Black Hole Thermodynamics

This file formalizes the laws of black hole thermodynamics, which establish a profound
connection between gravity, quantum mechanics, and thermodynamics.

## Main Definitions

* `BlackHole`: A black hole with mass, charge, and angular momentum
* `horizonArea`: The area of the event horizon
* `surfaceGravity`: The surface gravity κ at the horizon
* `hawkingTemperature`: The temperature T = ℏκ/(2πk_B)
* `bekensteinHawkingEntropy`: The entropy S = A/(4ℓ_P²)

## Laws of Black Hole Thermodynamics

* Zeroth Law: Surface gravity is constant over the horizon
* First Law: δM = (κ/8π)δA + ΩδJ + ΦδQ
* Second Law: The horizon area never decreases (classically)
* Third Law: Cannot reduce surface gravity to zero in finite steps

## Physical Background

Black holes behave like thermodynamic systems:
- Surface gravity κ ↔ Temperature T
- Horizon area A ↔ Entropy S
- Mass M ↔ Internal energy U

The Bekenstein-Hawking entropy S = A/(4ℓ_P²) implies black holes have enormous entropy
and connects quantum mechanics (ℏ), gravity (G), and thermodynamics.

## References

* Bekenstein, "Black holes and entropy" (1973)
* Hawking, "Particle creation by black holes" (1975)
* Wald, "General Relativity" (1984), Chapter 12
* MTW, "Gravitation" (1973), Chapter 33
-/

noncomputable section

namespace PseudoRiemannianMetric

/-! ## Black Hole Parameters -/

/-- A stationary black hole is characterized by mass M, angular momentum J, and charge Q.
By the no-hair theorem, these are the only independent parameters. -/
structure BlackHole where
  /-- The ADM mass of the black hole -/
  mass : ℝ
  /-- The angular momentum (0 for Schwarzschild) -/
  angularMomentum : ℝ
  /-- The electric charge (0 for uncharged black holes) -/
  charge : ℝ
  /-- Mass is positive -/
  mass_pos : mass > 0
  /-- The Kerr bound: a² + Q² ≤ M² (otherwise naked singularity) -/
  kerr_bound : (angularMomentum / mass)^2 + charge^2 ≤ mass^2

/-- The spin parameter a = J/M for a Kerr black hole. -/
def BlackHole.spinParameter (bh : BlackHole) : ℝ := bh.angularMomentum / bh.mass

/-- A Schwarzschild black hole has no spin or charge. -/
def BlackHole.isSchwarzschild (bh : BlackHole) : Prop :=
  bh.angularMomentum = 0 ∧ bh.charge = 0

/-- A Kerr black hole has spin but no charge. -/
def BlackHole.isKerr (bh : BlackHole) : Prop :=
  bh.charge = 0

/-- A Reissner-Nordström black hole has charge but no spin. -/
def BlackHole.isReissnerNordstrom (bh : BlackHole) : Prop :=
  bh.angularMomentum = 0

/-- An extremal black hole saturates the Kerr bound: a² + Q² = M². -/
def BlackHole.isExtremal (bh : BlackHole) : Prop :=
  bh.spinParameter^2 + bh.charge^2 = bh.mass^2

/-! ## Event Horizon Properties -/

/-- The event horizon radius for a Schwarzschild black hole: r_+ = 2M. -/
def schwarzschildHorizonRadius (bh : BlackHole) (_hS : bh.isSchwarzschild) : ℝ :=
  2 * bh.mass

/-- The outer horizon radius for a Kerr-Newman black hole:
r_+ = M + √(M² - a² - Q²) -/
def outerHorizonRadius (bh : BlackHole) : ℝ :=
  let discriminant := bh.mass^2 - bh.spinParameter^2 - bh.charge^2
  bh.mass + Real.sqrt (max discriminant 0)

/-- The outer horizon radius is positive. -/
lemma outerHorizonRadius_pos (bh : BlackHole) : outerHorizonRadius bh > 0 := by
  unfold outerHorizonRadius
  have hm : bh.mass > 0 := bh.mass_pos
  have hsqrt : Real.sqrt (max (bh.mass^2 - bh.spinParameter^2 - bh.charge^2) 0) ≥ 0 :=
    Real.sqrt_nonneg _
  linarith

/-- The inner (Cauchy) horizon radius for a Kerr-Newman black hole:
r_- = M - √(M² - a² - Q²) -/
def innerHorizonRadius (bh : BlackHole) : ℝ :=
  let discriminant := bh.mass^2 - bh.spinParameter^2 - bh.charge^2
  bh.mass - Real.sqrt (max discriminant 0)

/-- The area of the event horizon.
For Schwarzschild: A = 16πM² = 4πr_+²
For Kerr: A = 8πMr_+
General Kerr-Newman: A = 4π(r_+² + a²) -/
def horizonArea (bh : BlackHole) : ℝ :=
  let r_plus := outerHorizonRadius bh
  let a := bh.spinParameter
  4 * Real.pi * (r_plus^2 + a^2)

/-- The horizon area is positive. -/
lemma horizonArea_pos (bh : BlackHole) : horizonArea bh > 0 := by
  unfold horizonArea
  apply mul_pos
  · apply mul_pos; norm_num; exact Real.pi_pos
  · have hr : outerHorizonRadius bh > 0 := outerHorizonRadius_pos bh
    have h1 : (outerHorizonRadius bh)^2 > 0 := sq_pos_of_pos hr
    have h2 : bh.spinParameter^2 ≥ 0 := sq_nonneg _
    linarith

/-! ## Surface Gravity -/

/-- The surface gravity κ of a black hole.
For Schwarzschild: κ = 1/(4M)
For Kerr: κ = √(M² - a²)/(2Mr_+)
For extremal black holes: κ = 0 -/
def surfaceGravity (bh : BlackHole) : ℝ :=
  let a := bh.spinParameter
  let Q := bh.charge
  let discriminant := bh.mass^2 - a^2 - Q^2
  if discriminant > 0 then
    let r_plus := bh.mass + Real.sqrt discriminant
    Real.sqrt discriminant / (2 * bh.mass * r_plus)
  else
    0

/-- The surface gravity of a Schwarzschild black hole is 1/(4M). -/
lemma surfaceGravity_schwarzschild (bh : BlackHole) (hS : bh.isSchwarzschild) :
    surfaceGravity bh = 1 / (4 * bh.mass) := by
  unfold surfaceGravity BlackHole.spinParameter
  have hM_pos : bh.mass > 0 := bh.mass_pos
  have hM_sq_pos : bh.mass^2 > 0 := sq_pos_of_pos hM_pos
  simp only [hS.1, hS.2, zero_div]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero, hM_sq_pos,
    ↓reduceIte, Real.sqrt_sq (le_of_lt hM_pos)]
  field_simp
  ring

/-- The surface gravity is non-negative. -/
lemma surfaceGravity_nonneg (bh : BlackHole) : surfaceGravity bh ≥ 0 := by
  simp only [surfaceGravity]
  split_ifs with h
  · apply div_nonneg
    · exact Real.sqrt_nonneg _
    · have hm : bh.mass > 0 := bh.mass_pos
      have hsqrt : Real.sqrt (bh.mass ^ 2 - (bh.angularMomentum / bh.mass) ^ 2 -
          bh.charge ^ 2) ≥ 0 := Real.sqrt_nonneg _
      have hr : bh.mass + Real.sqrt (bh.mass ^ 2 - (bh.angularMomentum / bh.mass) ^ 2 -
          bh.charge ^ 2) > 0 := by
        linarith
      have h2 : 2 * bh.mass > 0 := by linarith
      exact le_of_lt (mul_pos h2 hr)
  · norm_num

/-! ## Hawking Temperature -/

/-- The Hawking temperature of a black hole:
T_H = ℏκ/(2πk_B)

In natural units (ℏ = k_B = 1): T_H = κ/(2π)

For Schwarzschild: T_H = 1/(8πM) -/
def hawkingTemperature (bh : BlackHole) : ℝ :=
  surfaceGravity bh / (2 * Real.pi)

/-- The Hawking temperature is non-negative. -/
lemma hawkingTemperature_nonneg (bh : BlackHole) : hawkingTemperature bh ≥ 0 := by
  unfold hawkingTemperature
  apply div_nonneg (surfaceGravity_nonneg bh)
  have h1 : (2 : ℝ) > 0 := by norm_num
  exact le_of_lt (mul_pos h1 Real.pi_pos)

/-- The Hawking temperature of a Schwarzschild black hole. -/
lemma hawkingTemperature_schwarzschild (bh : BlackHole) (hS : bh.isSchwarzschild) :
    hawkingTemperature bh = 1 / (8 * Real.pi * bh.mass) := by
  unfold hawkingTemperature
  rw [surfaceGravity_schwarzschild bh hS]
  ring

/-! ## Bekenstein-Hawking Entropy -/

/-- The Bekenstein-Hawking entropy:
S_BH = A/(4ℓ_P²) = A k_B c³/(4Gℏ)

In natural units (G = ℏ = k_B = c = 1): S_BH = A/4

This is an enormous entropy: for a solar-mass black hole, S ≈ 10⁷⁷ k_B. -/
def bekensteinHawkingEntropy (bh : BlackHole) : ℝ :=
  horizonArea bh / 4

/-- The entropy is positive. -/
lemma bekensteinHawkingEntropy_pos (bh : BlackHole) : bekensteinHawkingEntropy bh > 0 := by
  unfold bekensteinHawkingEntropy
  apply div_pos (horizonArea_pos bh)
  norm_num

/-- The entropy of a Schwarzschild black hole is S = 4πM². -/
lemma entropy_schwarzschild (bh : BlackHole) (hS : bh.isSchwarzschild) :
    bekensteinHawkingEntropy bh = 4 * Real.pi * bh.mass^2 := by
  unfold bekensteinHawkingEntropy horizonArea outerHorizonRadius BlackHole.spinParameter
  have hM_pos : bh.mass > 0 := bh.mass_pos
  have hM_sq_pos : bh.mass^2 > 0 := sq_pos_of_pos hM_pos
  simp only [hS.1, hS.2, zero_div]
  have hmax : max (bh.mass^2) 0 = bh.mass^2 := max_eq_left (le_of_lt hM_sq_pos)
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero, hmax,
    Real.sqrt_sq (le_of_lt hM_pos), add_zero]
  ring

/-! ## Hawking Radiation -/

/-- The power (luminosity) of Hawking radiation scales as T⁴ (Stefan-Boltzmann):
P ∝ A T⁴ ∝ 1/M²

For Schwarzschild: P = ℏc⁶/(15360πG²M²) -/
def hawkingLuminosity (bh : BlackHole) : ℝ :=
  1 / (15360 * Real.pi * bh.mass^2)

/-- The Hawking luminosity is positive. -/
lemma hawkingLuminosity_pos (bh : BlackHole) : hawkingLuminosity bh > 0 := by
  unfold hawkingLuminosity
  apply one_div_pos.mpr
  apply mul_pos
  · apply mul_pos; norm_num; exact Real.pi_pos
  · exact sq_pos_of_pos bh.mass_pos

/-- The evaporation time of a Schwarzschild black hole scales as M³. -/
def evaporationTime (bh : BlackHole) (_hS : bh.isSchwarzschild) : ℝ :=
  5120 * Real.pi * bh.mass^3

/-- The evaporation time is positive. -/
lemma evaporationTime_pos (bh : BlackHole) (hS : bh.isSchwarzschild) :
    evaporationTime bh hS > 0 := by
  unfold evaporationTime
  apply mul_pos
  · apply mul_pos; norm_num; exact Real.pi_pos
  · exact pow_pos bh.mass_pos 3

/-- The Page time: the time at which half the initial entropy has been radiated. -/
def pageTime (bh : BlackHole) (hS : bh.isSchwarzschild) : ℝ :=
  evaporationTime bh hS / 2

/-- The Page time is positive. -/
lemma pageTime_pos (bh : BlackHole) (hS : bh.isSchwarzschild) : pageTime bh hS > 0 := by
  unfold pageTime
  apply div_pos (evaporationTime_pos bh hS)
  norm_num

/-! ## Thermodynamic Relations -/

/-- The first law relates changes in mass to changes in area, angular momentum, and charge:
δM = (κ/8π)δA + Ω_H δJ + Φ_H δQ

This structure captures the coefficients in the first law. -/
structure FirstLawCoefficients (bh : BlackHole) where
  /-- κ/(8π) coefficient for area change -/
  areaCoeff : ℝ := surfaceGravity bh / (8 * Real.pi)
  /-- Horizon angular velocity Ω_H -/
  angularVelocity : ℝ
  /-- Electric potential at horizon Φ_H -/
  electricPotential : ℝ

/-- For Schwarzschild, the area coefficient is 1/(32πM). -/
lemma firstLaw_areaCoeff_schwarzschild (bh : BlackHole) (hS : bh.isSchwarzschild) :
    surfaceGravity bh / (8 * Real.pi) = 1 / (32 * Real.pi * bh.mass) := by
  rw [surfaceGravity_schwarzschild bh hS]
  ring

end PseudoRiemannianMetric
end
