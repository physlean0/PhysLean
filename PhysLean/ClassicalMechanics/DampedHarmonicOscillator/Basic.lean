/-
Copyright (c) 2025 Nicola Bernini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicola Bernini
-/
import PhysLean.Meta.Informal.SemiFormal
import PhysLean.ClassicalMechanics.EulerLagrange
import PhysLean.ClassicalMechanics.HamiltonsEquations
import PhysLean.ClassicalMechanics.HarmonicOscillator.Basic
/-!

# The Damped Harmonic Oscillator

## i. Overview

The damped harmonic oscillator is a classical mechanical system corresponding to a
mass `m` under a restoring force `- k x` and a damping force `- γ ẋ`, where `k` is the
spring constant, `γ` is the damping coefficient, `x` is the position, and `ẋ` is the velocity.

The equation of motion for the damped harmonic oscillator is:
```
m ẍ + γ ẋ + k x = 0
```

Depending on the relationship between the damping coefficient and the natural frequency,
the system exhibits three different behaviors:
- **Underdamped** (γ² < 4mk) : Oscillatory motion with exponentially decaying amplitude
- **Critically damped** (γ² = 4mk) : Fastest return to equilibrium without oscillation
- **Overdamped** (γ² > 4mk) : Slow return to equilibrium without oscillation

## ii. Key results

This module is currently a placeholder for future implementation. The following results
are planned to be formalized:

- `DampedHarmonicOscillator`: Structure containing the input data (mass, spring constant,
  damping coefficient)
- `EquationOfMotion`: The equation of motion for the damped harmonic oscillator
- Solutions for underdamped, critically damped, and overdamped cases
- Energy dissipation properties
- Quality factor and relaxation time

## iii. Table of contents

- A. The input data (to be implemented)
- B. The damped angular frequency (to be implemented)
- C. The energies and energy dissipation (to be implemented)
- D. The equation of motion (to be implemented)
- E. Solutions (to be implemented)
  - E.1. Underdamped case
  - E.2. Critically damped case
  - E.3. Overdamped case
- F. Quality factor and decay time (to be implemented)

## iv. References

References for the damped harmonic oscillator include:
- Landau & Lifshitz, Mechanics, page 76, section 25.
- Goldstein, Classical Mechanics, Chapter 2.

-/

namespace ClassicalMechanics
open Real
open Space
open InnerProductSpace
open MeasureTheory ContDiff Time

TODO "DHO04" "Prove the derivative relation: when x satisfies the equation of motion,
  Time.deriv (energy x) t = energyDissipationRate x t."

TODO "DHO08" "Prove additional properties of the quality factor Q, such as Q = ω₀/(2λ)."

TODO "DHO09" "Prove additional properties of the relaxation time τ, such as τ = 1/λ."

/-!

## A. The input data (placeholder)

The input data for the damped harmonic oscillator will consist of:
- Mass `m > 0`
- Spring constant `k > 0`
- Damping coefficient `γ ≥ 0`

-/

/-- Placeholder structure for the damped harmonic oscillator.
  The damped harmonic oscillator is specified by a mass `m`, a spring constant `k`,
  and a damping coefficient `γ`. All parameters are assumed to be positive (or non-negative
  for the damping coefficient). -/
structure DampedHarmonicOscillator where
  /-- The mass of the oscillator. -/
  m : ℝ
  /-- The spring constant of the oscillator. -/
  k : ℝ
  /-- The damping coefficient of the oscillator. -/
  γ : ℝ
  m_pos : 0 < m
  k_pos : 0 < k
  γ_nonneg : 0 ≤ γ

namespace DampedHarmonicOscillator

variable (S : DampedHarmonicOscillator)

@[simp]
lemma k_neq_zero : S.k ≠ 0 := Ne.symm (ne_of_lt S.k_pos)

@[simp]
lemma m_neq_zero : S.m ≠ 0 := Ne.symm (ne_of_lt S.m_pos)

/-!

## B. The natural angular frequency (placeholder)

The natural angular frequency ω₀ = √(k/m) will be defined here.

-/

/-- The natural (undamped) angular frequency of the oscillator, ω₀ = √(k/m). -/
noncomputable def ω₀ : ℝ := √(S.k / S.m)

@[simp]
lemma ω₀_pos : 0 < S.ω₀ := sqrt_pos.mpr (div_pos S.k_pos S.m_pos)

lemma ω₀_sq : S.ω₀^2 = S.k / S.m := by
  rw [ω₀, sq_sqrt]
  exact div_nonneg (le_of_lt S.k_pos) (le_of_lt S.m_pos)

/-!
## C. Equation of motion (Tag: DHO03)

The damped harmonic oscillator with mass `m`, spring
constant `k`, and damping coefficient `γ` satisfies

    m ẍ + γ ẋ + k x = 0,

where `x : Time → ℝ` is the position as a function of time.
-/

/-- The equation of motion for the damped harmonic oscillator.

A function `x : Time → ℝ` is a solution if it satisfies

    S.m * x¨ + S.γ * ẋ + S.k * x = 0

for all times `t`. -/
noncomputable def EquationOfMotion (x : Time → ℝ) : Prop :=
  ∀ t : Time,
    S.m * (Time.deriv (Time.deriv x) t) +
    S.γ * (Time.deriv x t) +
    S.k * x t = 0

/-!
## D. The energies and energy dissipation (Tag: DHO04)

For the damped harmonic oscillator, the mechanical energy is

  E(t) = ½ S.m (ẋ(t))^2 + ½ S.k (x(t))^2,

where `x : Time → ℝ` is the position as a function of time.

If `x` satisfies the equation of motion

  S.m * x¨ + S.γ * ẋ + S.k * x = 0,

then differentiating `E` with respect to time and substituting the
equation of motion yields

  dE/dt = - S.γ * (ẋ(t))^2 ≤ 0

Thus the energy is non-increasing in time, and it is strictly decreasing
whenever `S.γ > 0` and `ẋ(t) ≠ 0`. In particular, for `S.γ > 0`
the energy is not conserved, and the energy dissipation rate is
proportional to the squared velocity.
-/

/-- The kinetic energy of the damped harmonic oscillator. -/
noncomputable def kineticEnergy (x : Time → ℝ) : Time → ℝ :=
  fun t => (1 / 2 : ℝ) * S.m * (Time.deriv x t)^2

/-- The potential energy of the damped harmonic oscillator. -/
noncomputable def potentialEnergy (x : Time → ℝ) : Time → ℝ :=
  fun t => (1 / 2 : ℝ) * S.k * (x t)^2

/-- Mechanical energy of the damped harmonic oscillator. -/
noncomputable def energy (x : Time → ℝ) : Time → ℝ :=
  S.kineticEnergy x + S.potentialEnergy x

/-- Energy dissipation rate along a trajectory `x : Time → ℝ`.

  if `x` satisfies `S.equationOfMotion x`, then

  Time.deriv (S.energy x) t = - S.γ * (Time.deriv x t)^2,

so the energy is non-increasing and not conserved when `S.γ > 0`. -/
noncomputable def energyDissipationRate (x : Time → ℝ) : Time → ℝ :=
  fun t => - S.γ * (Time.deriv x t)^2

/-!
### D.1. Energy dissipation from the equation of motion

The key result is that when the equation of motion is satisfied, the time derivative
of energy equals the energy dissipation rate `-γ * ẋ²`. This follows from:
- Total energy E = (1/2)m*ẋ² + (1/2)k*x²
- dE/dt = m*ẋ*ẍ + k*x*ẋ = ẋ*(m*ẍ + k*x)
- From equation of motion: m*ẍ + γ*ẋ + k*x = 0, so m*ẍ + k*x = -γ*ẋ
- Therefore: dE/dt = ẋ*(-γ*ẋ) = -γ*ẋ² ≤ 0
-/

/-- When the equation of motion is satisfied, energy is dissipated at a rate
    proportional to the squared velocity. This is the key physical result
    showing that the damped oscillator loses energy to friction. -/
lemma energy_dissipation_rate_nonneg (x : Time → ℝ) (t : Time) :
    energyDissipationRate S x t ≤ 0 := by
  unfold energyDissipationRate
  have h1 : 0 ≤ (Time.deriv x t)^2 := sq_nonneg _
  have h2 : 0 ≤ S.γ := S.γ_nonneg
  nlinarith

/-!

## E. Damping regimes (placeholder)

The three damping regimes will be defined based on the discriminant γ² - 4mk.

-/

/-- The discriminant that determines the damping regime. -/
noncomputable def discriminant : ℝ := S.γ^2 - 4 * S.m * S.k

/-- The system is underdamped when γ² < 4mk. -/
def IsUnderdamped : Prop := S.discriminant < 0

/-- The system is critically damped when γ² = 4mk. -/
def IsCriticallyDamped : Prop := S.discriminant = 0

/-- The system is overdamped when γ² > 4mk. -/
def IsOverdamped : Prop := S.discriminant > 0

/-- The underdamped condition is equivalent to γ < 2√(mk). -/
lemma isUnderdamped_iff : S.IsUnderdamped ↔ S.γ < 2 * √(S.m * S.k) := by
  unfold IsUnderdamped discriminant
  have hmk_pos : 0 < S.m * S.k := mul_pos S.m_pos S.k_pos
  have h2sqrt_pos : 0 < 2 * √(S.m * S.k) := by positivity
  have h2 : (2 * √(S.m * S.k))^2 = 4 * S.m * S.k := by
    rw [mul_pow, sq_sqrt (le_of_lt hmk_pos)]
    ring
  constructor
  · intro h
    have h1 : S.γ^2 < 4 * S.m * S.k := by linarith
    have h3 : S.γ^2 < (2 * √(S.m * S.k))^2 := by rw [h2]; exact h1
    have hγ_nonneg : 0 ≤ S.γ := S.γ_nonneg
    have h2sqrt_nonneg : 0 ≤ 2 * √(S.m * S.k) := by positivity
    nlinarith [sq_nonneg (S.γ - 2 * √(S.m * S.k)), sq_nonneg (S.γ + 2 * √(S.m * S.k))]
  · intro h
    have hγ_nonneg : 0 ≤ S.γ := S.γ_nonneg
    have h2sqrt_nonneg : 0 ≤ 2 * √(S.m * S.k) := by positivity
    have h1 : S.γ^2 < (2 * √(S.m * S.k))^2 := by
      nlinarith [sq_nonneg (S.γ - 2 * √(S.m * S.k)), sq_nonneg (S.γ + 2 * √(S.m * S.k))]
    linarith [h1, h2]

/-- The critically damped condition is equivalent to γ = 2√(mk). -/
lemma isCriticallyDamped_iff : S.IsCriticallyDamped ↔ S.γ = 2 * √(S.m * S.k) := by
  unfold IsCriticallyDamped discriminant
  have hmk_pos : 0 < S.m * S.k := mul_pos S.m_pos S.k_pos
  have h2 : (2 * √(S.m * S.k))^2 = 4 * S.m * S.k := by
    rw [mul_pow, sq_sqrt (le_of_lt hmk_pos)]
    ring
  constructor
  · intro h
    have h1 : S.γ^2 = 4 * S.m * S.k := by linarith
    have h3 : S.γ^2 = (2 * √(S.m * S.k))^2 := by rw [h1, h2]
    have hγ_nonneg : 0 ≤ S.γ := S.γ_nonneg
    have h2sqrt_nonneg : 0 ≤ 2 * √(S.m * S.k) := by positivity
    have h4 : (S.γ - 2 * √(S.m * S.k)) * (S.γ + 2 * √(S.m * S.k)) = 0 := by nlinarith [h3]
    rcases mul_eq_zero.mp h4 with hsub | hadd
    · linarith
    · nlinarith
  · intro h
    rw [h, mul_pow, sq_sqrt (le_of_lt hmk_pos)]
    ring

/-- The overdamped condition is equivalent to γ > 2√(mk). -/
lemma isOverdamped_iff : S.IsOverdamped ↔ S.γ > 2 * √(S.m * S.k) := by
  unfold IsOverdamped discriminant
  have hmk_pos : 0 < S.m * S.k := mul_pos S.m_pos S.k_pos
  have h2 : (2 * √(S.m * S.k))^2 = 4 * S.m * S.k := by
    rw [mul_pow, sq_sqrt (le_of_lt hmk_pos)]
    ring
  constructor
  · intro h
    have h1 : S.γ^2 > 4 * S.m * S.k := by linarith
    have h3 : S.γ^2 > (2 * √(S.m * S.k))^2 := by rw [h2]; exact h1
    have hγ_nonneg : 0 ≤ S.γ := S.γ_nonneg
    have h2sqrt_nonneg : 0 ≤ 2 * √(S.m * S.k) := by positivity
    nlinarith [sq_nonneg (S.γ - 2 * √(S.m * S.k)), sq_nonneg (S.γ + 2 * √(S.m * S.k))]
  · intro h
    have hγ_nonneg : 0 ≤ S.γ := S.γ_nonneg
    have h2sqrt_nonneg : 0 ≤ 2 * √(S.m * S.k) := by positivity
    have h1 : S.γ^2 > (2 * √(S.m * S.k))^2 := by
      nlinarith [sq_nonneg (S.γ - 2 * √(S.m * S.k)), sq_nonneg (S.γ + 2 * √(S.m * S.k))]
    linarith [h1, h2]

/-!

### E.1. The damped angular frequency

For an underdamped oscillator, the damped angular frequency ωd characterizes the
oscillation frequency of the decaying motion. It is given by:

  ωd = √(ω₀² - (γ/(2m))²) = √(k/m - γ²/(4m²))

This is real and positive when the system is underdamped.

-/

/-- The damped angular frequency squared. This is positive when underdamped. -/
noncomputable def ωd_sq : ℝ := S.k / S.m - S.γ^2 / (4 * S.m^2)

/-- Alternative form: ωd² = ω₀² - (γ/(2m))². -/
lemma ωd_sq_eq : S.ωd_sq = S.ω₀^2 - (S.γ / (2 * S.m))^2 := by
  unfold ωd_sq ω₀
  rw [sq_sqrt (div_nonneg (le_of_lt S.k_pos) (le_of_lt S.m_pos))]
  field_simp
  ring

/-- The damped angular frequency squared is positive when underdamped. -/
lemma ωd_sq_pos (h : S.IsUnderdamped) : 0 < S.ωd_sq := by
  unfold ωd_sq IsUnderdamped discriminant at *
  have hm_sq_pos : 0 < S.m^2 := sq_pos_of_pos S.m_pos
  have h1 : S.γ^2 < 4 * S.m * S.k := by linarith
  have h2 : S.γ^2 / (4 * S.m^2) < (4 * S.m * S.k) / (4 * S.m^2) := by
    apply div_lt_div_of_pos_right h1
    positivity
  have h3 : (4 * S.m * S.k) / (4 * S.m^2) = S.k / S.m := by field_simp
  linarith [h2, h3]

/-- The damped angular frequency for an underdamped oscillator. -/
noncomputable def ωd (_ : S.IsUnderdamped) : ℝ := √S.ωd_sq

/-- The damped angular frequency is positive for underdamped systems. -/
@[simp]
lemma ωd_pos (h : S.IsUnderdamped) : 0 < S.ωd h := sqrt_pos.mpr (S.ωd_sq_pos h)

/-- The damped angular frequency squared equals ωd². -/
lemma ωd_sq_eq_sq (h : S.IsUnderdamped) : (S.ωd h)^2 = S.ωd_sq :=
  sq_sqrt (le_of_lt (S.ωd_sq_pos h))

/-- The damped frequency is less than the natural frequency when γ > 0. -/
lemma ωd_lt_ω₀ (h : S.IsUnderdamped) (hγ : 0 < S.γ) : S.ωd h < S.ω₀ := by
  have h1 : (S.ωd h)^2 < S.ω₀^2 := by
    rw [ωd_sq_eq_sq, ωd_sq_eq]
    have hm_pos : 0 < S.m := S.m_pos
    have hpos : 0 < (S.γ / (2 * S.m))^2 := by
      apply sq_pos_of_pos
      apply div_pos hγ
      linarith
    linarith
  have h2 : 0 < S.ωd h := S.ωd_pos h
  have h3 : 0 < S.ω₀ := S.ω₀_pos
  nlinarith [sq_nonneg (S.ωd h - S.ω₀), sq_nonneg (S.ωd h + S.ω₀)]

/-!

## F. Quality factor and relaxation time

The quality factor Q and relaxation time τ characterize the damping behavior.

-/

/-- The damping ratio ζ = γ / (2√(mk)) characterizes the damping relative to critical damping.
    - ζ < 1: underdamped
    - ζ = 1: critically damped
    - ζ > 1: overdamped -/
noncomputable def dampingRatio : ℝ := S.γ / (2 * √(S.m * S.k))

/-- The quality factor Q = √(mk) / γ measures the "sharpness" of resonance.
    Higher Q means lower damping and sharper resonance.
    Only meaningful when γ > 0. -/
noncomputable def qualityFactor (_ : S.γ > 0) : ℝ := √(S.m * S.k) / S.γ

/-- The relaxation time τ = 2m / γ is the characteristic decay time.
    Energy decays as e^(-t/τ). Only meaningful when γ > 0. -/
noncomputable def relaxationTime (_ : S.γ > 0) : ℝ := 2 * S.m / S.γ

@[simp]
lemma qualityFactor_pos (hγ : S.γ > 0) : 0 < S.qualityFactor hγ := by
  unfold qualityFactor
  apply div_pos
  · exact sqrt_pos.mpr (mul_pos S.m_pos S.k_pos)
  · exact hγ

@[simp]
lemma relaxationTime_pos (hγ : S.γ > 0) : 0 < S.relaxationTime hγ := by
  unfold relaxationTime
  apply div_pos
  · exact mul_pos (by norm_num : (0 : ℝ) < 2) S.m_pos
  · exact hγ

/-- The damping ratio equals 1/(2Q). -/
lemma dampingRatio_eq_inv_twice_qualityFactor (hγ : S.γ > 0) :
    S.dampingRatio = 1 / (2 * S.qualityFactor hγ) := by
  unfold dampingRatio qualityFactor
  field_simp

/-!

## G. Reduction to undamped case

When γ = 0, the damped harmonic oscillator reduces to the undamped harmonic oscillator.

-/

/-- Convert a damped harmonic oscillator with γ = 0 to an undamped harmonic oscillator. -/
def toHarmonicOscillator (_ : S.γ = 0) : HarmonicOscillator where
  m := S.m
  k := S.k
  m_pos := S.m_pos
  k_pos := S.k_pos

/-- The natural frequency of the damped oscillator equals the frequency of the
    corresponding undamped oscillator. -/
lemma ω₀_eq_toHarmonicOscillator_ω (_ : S.γ = 0) :
    S.ω₀ = (S.toHarmonicOscillator ‹_›).ω := rfl

/-- When γ = 0, the equation of motion reduces to the undamped equation m ẍ + k x = 0. -/
lemma equationOfMotion_undamped (hγ : S.γ = 0) (x : Time → ℝ) :
    S.EquationOfMotion x ↔
    ∀ t : Time, S.m * (Time.deriv (Time.deriv x) t) + S.k * x t = 0 := by
  unfold EquationOfMotion
  simp only [hγ, zero_mul, add_zero]

/-- When γ = 0, energy is conserved (dissipation rate is zero). -/
lemma energyDissipationRate_zero_when_undamped (hγ : S.γ = 0) (x : Time → ℝ) (t : Time) :
    S.energyDissipationRate x t = 0 := by
  simp only [energyDissipationRate, hγ, zero_mul, neg_zero]

/-!

## H. Underdamped Solutions (Tag: DHO05)

For an underdamped oscillator (γ² < 4mk), the general solution is:

  x(t) = A * exp(-γt/(2m)) * cos(ωd * t + φ)

where:
- A is the amplitude (determined by initial conditions)
- φ is the phase (determined by initial conditions)
- γ/(2m) is the decay rate
- ωd = √(k/m - γ²/(4m²)) is the damped angular frequency

This describes oscillatory motion with exponentially decaying amplitude.

-/

/-- The decay rate λ = γ/(2m) for the exponential envelope of underdamped motion. -/
noncomputable def decayRate : ℝ := S.γ / (2 * S.m)

@[simp]
lemma decayRate_nonneg : 0 ≤ S.decayRate := by
  unfold decayRate
  apply div_nonneg S.γ_nonneg
  linarith [S.m_pos]

@[simp]
lemma decayRate_pos (hγ : 0 < S.γ) : 0 < S.decayRate := by
  unfold decayRate
  apply div_pos hγ
  linarith [S.m_pos]

/-- The exponential decay envelope e^(-λt) for underdamped motion. -/
noncomputable def decayEnvelope : Time → ℝ := fun t => exp (-S.decayRate * t)

/-- The oscillating factor cos(ωd*t + φ) for underdamped motion. -/
noncomputable def oscillatingFactor (h : S.IsUnderdamped) (φ : ℝ) : Time → ℝ :=
  fun t => cos (S.ωd h * t + φ)

/-- The underdamped solution with amplitude A and phase φ.
    x(t) = A * exp(-λt) * cos(ωd * t + φ) where λ = γ/(2m). -/
noncomputable def underdampedSolution (h : S.IsUnderdamped) (A φ : ℝ) : Time → ℝ :=
  fun t => A * S.decayEnvelope t * S.oscillatingFactor h φ t

/-- The velocity of the underdamped solution. -/
noncomputable def underdampedVelocity (h : S.IsUnderdamped) (A φ : ℝ) : Time → ℝ :=
  fun t => A * S.decayEnvelope t *
    (- S.decayRate * cos (S.ωd h * t + φ) - S.ωd h * sin (S.ωd h * t + φ))

/-- The decay envelope is differentiable. -/
lemma decayEnvelope_differentiable : Differentiable ℝ S.decayEnvelope := by
  unfold decayEnvelope
  fun_prop

/-- The oscillating factor is differentiable. -/
lemma oscillatingFactor_differentiable (h : S.IsUnderdamped) (φ : ℝ) :
    Differentiable ℝ (S.oscillatingFactor h φ) := by
  unfold oscillatingFactor
  fun_prop

/-- The underdamped solution is differentiable. -/
lemma underdampedSolution_differentiable (h : S.IsUnderdamped) (A φ : ℝ) :
    Differentiable ℝ (S.underdampedSolution h A φ) := by
  unfold underdampedSolution decayEnvelope oscillatingFactor
  fun_prop

/-- The velocity of the underdamped solution is differentiable. -/
lemma underdampedVelocity_differentiable (h : S.IsUnderdamped) (A φ : ℝ) :
    Differentiable ℝ (S.underdampedVelocity h A φ) := by
  unfold underdampedVelocity decayEnvelope
  fun_prop

/-- The underdamped solution at t = 0 gives A * cos(φ). -/
lemma underdampedSolution_at_zero (h : S.IsUnderdamped) (A φ : ℝ) :
    S.underdampedSolution h A φ 0 = A * cos φ := by
  simp [underdampedSolution, decayEnvelope, oscillatingFactor]

/-- The underdamped velocity at t = 0. -/
lemma underdampedVelocity_at_zero (h : S.IsUnderdamped) (A φ : ℝ) :
    S.underdampedVelocity h A φ 0 = A * (-S.decayRate * cos φ - S.ωd h * sin φ) := by
  simp [underdampedVelocity, decayEnvelope]

/-- The decay envelope is always positive. -/
lemma decayEnvelope_pos (t : Time) : 0 < S.decayEnvelope t := by
  unfold decayEnvelope
  exact exp_pos _

/-- The amplitude of underdamped oscillation decays exponentially.
    After time t, the amplitude is reduced by factor e^(-λt). -/
lemma underdampedSolution_amplitude_decay (h : S.IsUnderdamped) (A φ : ℝ) (t : Time) :
    |S.underdampedSolution h A φ t| ≤ |A| * S.decayEnvelope t := by
  unfold underdampedSolution oscillatingFactor decayEnvelope
  have hcos : |cos (S.ωd h * t + φ)| ≤ 1 := abs_cos_le_one _
  have hexp_pos : 0 < exp (-S.decayRate * t) := exp_pos _
  calc |A * exp (-S.decayRate * t) * cos (S.ωd h * t + φ)|
      = |A| * |exp (-S.decayRate * t)| * |cos (S.ωd h * t + φ)| := by rw [abs_mul, abs_mul]
    _ = |A| * exp (-S.decayRate * t) * |cos (S.ωd h * t + φ)| := by
        rw [abs_of_pos hexp_pos]
    _ ≤ |A| * exp (-S.decayRate * t) * 1 := by
        apply mul_le_mul_of_nonneg_left hcos
        apply mul_nonneg (abs_nonneg _) (le_of_lt hexp_pos)
    _ = |A| * exp (-S.decayRate * t) := by ring

/-- The period of underdamped oscillation is T = 2π/ωd. -/
noncomputable def underdampedPeriod (h : S.IsUnderdamped) : ℝ := 2 * π / S.ωd h

lemma underdampedPeriod_pos (h : S.IsUnderdamped) : 0 < S.underdampedPeriod h := by
  unfold underdampedPeriod
  apply div_pos
  · exact mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos
  · exact S.ωd_pos h

/-!

## I. Critically Damped Solutions (Tag: DHO06)

For a critically damped oscillator (γ² = 4mk), the general solution is:

  x(t) = (A + B*t) * exp(-λt)

where:
- A and B are constants determined by initial conditions
- λ = γ/(2m) = ω₀ (at critical damping)

This is the fastest non-oscillatory return to equilibrium. The solution
approaches zero without overshooting.

At critical damping: λ = γ/(2m) = √(k/m) = ω₀

-/

/-- At critical damping, the decay rate equals the natural frequency. -/
lemma decayRate_eq_ω₀_of_criticallyDamped (h : S.IsCriticallyDamped) :
    S.decayRate = S.ω₀ := by
  unfold decayRate ω₀
  rw [isCriticallyDamped_iff] at h
  rw [h]
  have hmk_pos : 0 < S.m * S.k := mul_pos S.m_pos S.k_pos
  have hm_pos : 0 < S.m := S.m_pos
  have hm_ne : S.m ≠ 0 := ne_of_gt hm_pos
  -- Need to show: 2 * √(m*k) / (2 * m) = √(k/m)
  -- Simplify: √(m*k) / m = √(k/m)
  -- Use √(m*k) = √m * √k and √(k/m) = √k / √m
  rw [mul_div_mul_left _ _ (two_ne_zero)]
  rw [Real.sqrt_mul (le_of_lt S.m_pos) S.k]
  rw [Real.sqrt_div (le_of_lt S.k_pos)]
  have hsqrt_m : √S.m ^ 2 = S.m := Real.sq_sqrt (le_of_lt S.m_pos)
  field_simp [Real.sqrt_ne_zero'.mpr S.m_pos]
  rw [hsqrt_m]
  ring

/-- The critically damped solution with constants A and B.
    x(t) = (A + B*t) * exp(-λt) where λ = γ/(2m). -/
noncomputable def criticallyDampedSolution (_ : S.IsCriticallyDamped) (A B : ℝ) : Time → ℝ :=
  fun t => (A + B * t) * exp (-S.decayRate * t)

/-- The velocity of the critically damped solution. -/
noncomputable def criticallyDampedVelocity (_ : S.IsCriticallyDamped) (A B : ℝ) : Time → ℝ :=
  fun t => (B - S.decayRate * (A + B * t)) * exp (-S.decayRate * t)

/-- The critically damped solution is differentiable. -/
lemma criticallyDampedSolution_differentiable (h : S.IsCriticallyDamped) (A B : ℝ) :
    Differentiable ℝ (S.criticallyDampedSolution h A B) := by
  unfold criticallyDampedSolution
  fun_prop

/-- The velocity of the critically damped solution is differentiable. -/
lemma criticallyDampedVelocity_differentiable (h : S.IsCriticallyDamped) (A B : ℝ) :
    Differentiable ℝ (S.criticallyDampedVelocity h A B) := by
  unfold criticallyDampedVelocity
  fun_prop

/-- The critically damped solution at t = 0 gives A. -/
lemma criticallyDampedSolution_at_zero (h : S.IsCriticallyDamped) (A B : ℝ) :
    S.criticallyDampedSolution h A B 0 = A := by
  simp [criticallyDampedSolution]

/-- The critically damped velocity at t = 0 gives B - λA. -/
lemma criticallyDampedVelocity_at_zero (h : S.IsCriticallyDamped) (A B : ℝ) :
    S.criticallyDampedVelocity h A B 0 = B - S.decayRate * A := by
  simp [criticallyDampedVelocity]

/-- Given initial position x₀ and velocity v₀, the constants A and B are:
    A = x₀, B = v₀ + decayRate*x₀ -/
lemma criticallyDamped_initial_conditions (h : S.IsCriticallyDamped) (x₀ v₀ : ℝ) :
    let A := x₀
    let B := v₀ + S.decayRate * x₀
    S.criticallyDampedSolution h A B 0 = x₀ ∧
    S.criticallyDampedVelocity h A B 0 = v₀ := by
  constructor
  · -- Position: (A + B*0) * exp(0) = A = x₀
    rw [criticallyDampedSolution_at_zero]
  · -- Velocity: B - λA = (v₀ + λx₀) - λx₀ = v₀
    rw [criticallyDampedVelocity_at_zero]
    ring

/-!

## J. Overdamped Solutions (Tag: DHO07)

For an overdamped oscillator (γ² > 4mk), the general solution is:

  x(t) = A * exp(-λ₁ * t) + B * exp(-λ₂ * t)

where:
- λ₁ = (γ + √(γ² - 4mk)) / (2m) (faster decay rate)
- λ₂ = (γ - √(γ² - 4mk)) / (2m) (slower decay rate)

Both λ₁ > λ₂ > 0, so both terms decay exponentially but at different rates.
The solution approaches equilibrium without oscillation.

Alternatively, using λ = γ/(2m) and δ = √(γ² - 4mk) / (2m):
- λ₁ = λ + δ
- λ₂ = λ - δ

-/

/-- The overdamped discriminant square root: √(γ² - 4mk) / (2m).
    This is well-defined and positive when the system is overdamped. -/
noncomputable def overdampedDelta (_ : S.IsOverdamped) : ℝ :=
  √S.discriminant / (2 * S.m)

/-- The overdamped discriminant square root is positive. -/
lemma overdampedDelta_pos (h : S.IsOverdamped) : 0 < S.overdampedDelta h := by
  unfold overdampedDelta
  apply div_pos
  · exact sqrt_pos.mpr h
  · linarith [S.m_pos]

/-- The faster decay rate λ₁ = λ + δ = (γ + √(γ² - 4mk)) / (2m). -/
noncomputable def overdampedLambda1 (h : S.IsOverdamped) : ℝ :=
  S.decayRate + S.overdampedDelta h

/-- The slower decay rate λ₂ = λ - δ = (γ - √(γ² - 4mk)) / (2m). -/
noncomputable def overdampedLambda2 (h : S.IsOverdamped) : ℝ :=
  S.decayRate - S.overdampedDelta h

/-- The faster decay rate λ₁ is positive. -/
@[simp]
lemma overdampedLambda1_pos (h : S.IsOverdamped) : 0 < S.overdampedLambda1 h := by
  unfold overdampedLambda1
  have h1 : 0 ≤ S.decayRate := S.decayRate_nonneg
  have h2 : 0 < S.overdampedDelta h := S.overdampedDelta_pos h
  linarith

/-- The slower decay rate λ₂ is positive. -/
@[simp]
lemma overdampedLambda2_pos (h : S.IsOverdamped) : 0 < S.overdampedLambda2 h := by
  unfold overdampedLambda2 decayRate overdampedDelta discriminant
  -- Need: γ/(2m) > √(γ² - 4mk)/(2m)
  -- i.e., γ > √(γ² - 4mk)
  have hm_pos : 0 < S.m := S.m_pos
  have hγ_nonneg : 0 ≤ S.γ := S.γ_nonneg
  have hdisc_pos : 0 < S.γ^2 - 4 * S.m * S.k := h
  -- γ² > γ² - 4mk means 0 < 4mk, which is true
  have hmk_pos : 0 < 4 * S.m * S.k := by linarith [mul_pos S.m_pos S.k_pos]
  have h1 : S.γ^2 - 4 * S.m * S.k < S.γ^2 := by linarith
  have h2 : √(S.γ^2 - 4 * S.m * S.k) < √(S.γ^2) := by
    apply sqrt_lt_sqrt (le_of_lt hdisc_pos) h1
  have h3 : √(S.γ^2) = |S.γ| := sqrt_sq_eq_abs S.γ
  have h4 : |S.γ| = S.γ := abs_of_nonneg hγ_nonneg
  rw [h3, h4] at h2
  calc S.γ / (2 * S.m) - √(S.γ ^ 2 - 4 * S.m * S.k) / (2 * S.m)
      = (S.γ - √(S.γ ^ 2 - 4 * S.m * S.k)) / (2 * S.m) := by ring
    _ > 0 := by
        apply div_pos
        · linarith
        · linarith

/-- λ₁ > λ₂ (the faster rate is indeed faster). -/
lemma overdampedLambda1_gt_lambda2 (h : S.IsOverdamped) :
    S.overdampedLambda1 h > S.overdampedLambda2 h := by
  unfold overdampedLambda1 overdampedLambda2
  have hδ_pos : 0 < S.overdampedDelta h := S.overdampedDelta_pos h
  linarith

/-- λ₁ * λ₂ = ω₀² (product of decay rates equals natural frequency squared). -/
lemma overdampedLambda_product (h : S.IsOverdamped) :
    S.overdampedLambda1 h * S.overdampedLambda2 h = S.ω₀^2 := by
  unfold overdampedLambda1 overdampedLambda2 decayRate overdampedDelta ω₀ discriminant
  have hm_pos : 0 < S.m := S.m_pos
  have hm_ne : S.m ≠ 0 := ne_of_gt hm_pos
  have hdisc_nonneg : 0 ≤ S.γ^2 - 4 * S.m * S.k := le_of_lt h
  -- Note: Lean normalizes 4 * S.m * S.k to S.m * 4 * S.k after field_simp
  have hdisc_nonneg' : 0 ≤ S.γ^2 - S.m * 4 * S.k := by linarith
  -- (λ + δ)(λ - δ) = λ² - δ² = γ²/(4m²) - (γ² - 4mk)/(4m²) = mk/m² = k/m = ω₀²
  have hsq : (√(S.γ ^ 2 - S.m * 4 * S.k))^2 = S.γ ^ 2 - S.m * 4 * S.k := by
    apply sq_sqrt hdisc_nonneg'
  have hkm_nonneg : 0 ≤ S.k / S.m := div_nonneg (le_of_lt S.k_pos) (le_of_lt S.m_pos)
  rw [sq_sqrt hkm_nonneg]
  field_simp [hm_ne]
  calc (S.γ + √(S.γ ^ 2 - S.m * 4 * S.k)) * (S.γ - √(S.γ ^ 2 - S.m * 4 * S.k))
      = S.γ^2 - (√(S.γ ^ 2 - S.m * 4 * S.k))^2 := by ring
    _ = S.γ^2 - (S.γ ^ 2 - S.m * 4 * S.k) := by rw [hsq]
    _ = S.m * 4 * S.k := by ring
    _ = 2 ^ 2 * S.m * S.k := by ring

/-- λ₁ + λ₂ = 2λ = γ/m (sum of decay rates). -/
lemma overdampedLambda_sum (h : S.IsOverdamped) :
    S.overdampedLambda1 h + S.overdampedLambda2 h = S.γ / S.m := by
  unfold overdampedLambda1 overdampedLambda2 decayRate
  have hm_pos : 0 < S.m := S.m_pos
  have hm_ne : S.m ≠ 0 := ne_of_gt hm_pos
  field_simp
  ring

/-- The overdamped solution with constants A and B.
    x(t) = A * exp(-λ₁ * t) + B * exp(-λ₂ * t). -/
noncomputable def overdampedSolution (h : S.IsOverdamped) (A B : ℝ) : Time → ℝ :=
  fun t => A * exp (-S.overdampedLambda1 h * t) + B * exp (-S.overdampedLambda2 h * t)

/-- The velocity of the overdamped solution. -/
noncomputable def overdampedVelocity (h : S.IsOverdamped) (A B : ℝ) : Time → ℝ :=
  fun t => -S.overdampedLambda1 h * A * exp (-S.overdampedLambda1 h * t)
         - S.overdampedLambda2 h * B * exp (-S.overdampedLambda2 h * t)

/-- The overdamped solution is differentiable. -/
lemma overdampedSolution_differentiable (h : S.IsOverdamped) (A B : ℝ) :
    Differentiable ℝ (S.overdampedSolution h A B) := by
  unfold overdampedSolution
  fun_prop

/-- The velocity of the overdamped solution is differentiable. -/
lemma overdampedVelocity_differentiable (h : S.IsOverdamped) (A B : ℝ) :
    Differentiable ℝ (S.overdampedVelocity h A B) := by
  unfold overdampedVelocity
  fun_prop

/-- The overdamped solution at t = 0 gives A + B. -/
lemma overdampedSolution_at_zero (h : S.IsOverdamped) (A B : ℝ) :
    S.overdampedSolution h A B 0 = A + B := by
  simp [overdampedSolution]

/-- The overdamped velocity at t = 0 gives -λ₁A - λ₂B. -/
lemma overdampedVelocity_at_zero (h : S.IsOverdamped) (A B : ℝ) :
    S.overdampedVelocity h A B 0 = -S.overdampedLambda1 h * A - S.overdampedLambda2 h * B := by
  simp [overdampedVelocity]

/-- Given initial position x₀ and velocity v₀, the constants A and B are:
    A = (v₀ + λ₂*x₀) / (λ₂ - λ₁)
    B = (v₀ + λ₁*x₀) / (λ₁ - λ₂)
    which simplify to
    A = -(v₀ + λ₂*x₀) / (λ₁ - λ₂)
    B = (v₀ + λ₁*x₀) / (λ₁ - λ₂) -/
lemma overdamped_initial_conditions (h : S.IsOverdamped) (x₀ v₀ : ℝ) :
    let dL := S.overdampedLambda1 h - S.overdampedLambda2 h
    let A := -(v₀ + S.overdampedLambda2 h * x₀) / dL
    let B := (v₀ + S.overdampedLambda1 h * x₀) / dL
    S.overdampedSolution h A B 0 = x₀ ∧
    S.overdampedVelocity h A B 0 = v₀ := by
  have hdL_pos : 0 < S.overdampedLambda1 h - S.overdampedLambda2 h := by
    have := S.overdampedLambda1_gt_lambda2 h
    linarith
  have hdL_ne : S.overdampedLambda1 h - S.overdampedLambda2 h ≠ 0 := ne_of_gt hdL_pos
  constructor
  · -- Position: A + B = x₀
    rw [overdampedSolution_at_zero]
    field_simp
    ring
  · -- Velocity: -λ₁A - λ₂B = v₀
    rw [overdampedVelocity_at_zero]
    field_simp
    ring

/-- The overdamped solution always decays to zero as t → ∞.
    Note: We state this for the underlying real function via Time.val. -/
lemma overdampedSolution_tendsto_zero (h : S.IsOverdamped) (A B : ℝ) :
    Filter.Tendsto (fun t : ℝ => S.overdampedSolution h A B ⟨t⟩) Filter.atTop (nhds 0) := by
  unfold overdampedSolution
  simp only
  have hL1_pos : 0 < S.overdampedLambda1 h := S.overdampedLambda1_pos h
  have hL2_pos : 0 < S.overdampedLambda2 h := S.overdampedLambda2_pos h
  have h1 : Filter.Tendsto (fun t : ℝ => A * exp (-S.overdampedLambda1 h * t))
      Filter.atTop (nhds 0) := by
    have hexp : Filter.Tendsto (fun t : ℝ => exp (-S.overdampedLambda1 h * t))
        Filter.atTop (nhds 0) := by
      have := tendsto_exp_neg_atTop_nhds_zero.comp
        (Filter.Tendsto.const_mul_atTop hL1_pos Filter.tendsto_id)
      convert this using 1
      ext t
      simp [mul_comm]
    convert Filter.Tendsto.const_mul A hexp using 2
    simp
  have h2 : Filter.Tendsto (fun t : ℝ => B * exp (-S.overdampedLambda2 h * t))
      Filter.atTop (nhds 0) := by
    have hexp : Filter.Tendsto (fun t : ℝ => exp (-S.overdampedLambda2 h * t))
        Filter.atTop (nhds 0) := by
      have := tendsto_exp_neg_atTop_nhds_zero.comp
        (Filter.Tendsto.const_mul_atTop hL2_pos Filter.tendsto_id)
      convert this using 1
      ext t
      simp [mul_comm]
    convert Filter.Tendsto.const_mul B hexp using 2
    simp
  convert h1.add h2 using 2
  simp

end DampedHarmonicOscillator

end ClassicalMechanics
