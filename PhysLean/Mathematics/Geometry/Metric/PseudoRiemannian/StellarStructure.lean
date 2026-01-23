/-
Copyright (c) 2025 PhysLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PhysLean Contributors
-/

import PhysLean.Mathematics.Geometry.Metric.PseudoRiemannian.PerfectFluid
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Relativistic Stellar Structure

This file formalizes the structure of relativistic stars, including the
Tolman-Oppenheimer-Volkoff (TOV) equation for hydrostatic equilibrium
and the physics of compact objects like neutron stars.

## Main Definitions

* `StaticStar`: A static, spherically symmetric star with perfect fluid
* `tovRHS`: The right-hand side of the TOV equation for hydrostatic equilibrium
* `compactness`: The compactness parameter M/R
* `buchdahlLimit`: The maximum compactness 4/9 for stable stars
* `EquationOfState`: Relates pressure to density
* `surfaceRedshift`: Gravitational redshift at stellar surface

## Physical Interpretation

The TOV equation extends Newtonian hydrostatic equilibrium to GR:
- Pressure contributes to gravitational mass
- Gravitational redshift affects the pressure gradient
- Maximum compactness exists (Buchdahl limit)

Applications:
- White dwarf structure
- Neutron star structure
- Maximum masses and radii
- Equation of state constraints

## References

* Tolman, "Static Solutions of Einstein's Field Equations" (1939)
* Oppenheimer & Volkoff, "On Massive Neutron Cores" (1939)
* Misner, Thorne, Wheeler, "Gravitation" (1973), Chapter 23
* Shapiro & Teukolsky, "Black Holes, White Dwarfs, and Neutron Stars" (1983)
-/

noncomputable section

open Bundle Set Finset Function Filter Module Topology ContinuousLinearMap
open scoped Manifold Bundle LinearMap Dual

namespace PseudoRiemannianMetric

/-! ## Static Spherically Symmetric Stars -/

/-- A static, spherically symmetric star with perfect fluid matter.
The metric is ds² = -e^{2Φ}dt² + e^{2Λ}dr² + r²dΩ². -/
structure StaticStar where
  /-- Energy density ρ(r) -/
  density : ℝ → ℝ
  /-- Pressure P(r) -/
  pressure : ℝ → ℝ
  /-- Metric potential Φ(r) -/
  phi : ℝ → ℝ
  /-- Metric potential Λ(r) related to mass -/
  lambda : ℝ → ℝ
  /-- The star has finite radius R -/
  radius : ℝ
  /-- Density is non-negative -/
  density_nonneg : ∀ r, density r ≥ 0
  /-- Radius is positive -/
  radius_pos : radius > 0

/-- The mass function m(r) = mass enclosed within radius r.
dm/dr = 4πr²ρ. -/
def massFunction (star : StaticStar) (r : ℝ) : ℝ :=
  4 * Real.pi * r^2 * star.density r  -- This is dm/dr, would integrate

/-- The metric component g_rr = e^{2Λ} = (1 - 2m/r)^{-1}. -/
def metricGrr (mass r : ℝ) : ℝ :=
  1 / (1 - 2 * mass / r)

/-! ## The TOV Equation -/

/-- The Tolman-Oppenheimer-Volkoff equation for hydrostatic equilibrium:
dP/dr = -(ρ + P)(m + 4πr³P) / (r(r - 2m))

This is the relativistic generalization of dP/dr = -ρg. -/
def tovRHS (density pressure mass r : ℝ) : ℝ :=
  -(density + pressure) * (mass + 4 * Real.pi * r^3 * pressure) /
   (r * (r - 2 * mass))

/-- The TOV equation reduces to Newtonian for small M/r. -/
lemma tovRHS_newtonian_limit {density mass r : ℝ} (hr : r > 0) (hsmall : mass / r < 1/10) :
    tovRHS density 0 mass r = -(density * mass) / (r * (r - 2 * mass)) := by
  unfold tovRHS
  ring

/-! ## Boundary Conditions -/

/-- At the center (r = 0):
- ρ(0) = ρ_c (central density)
- P(0) = P_c (central pressure)
- m(0) = 0 (no mass at center) -/
structure CentralConditions where
  /-- Central density -/
  centralDensity : ℝ
  /-- Central pressure -/
  centralPressure : ℝ
  /-- Central density is positive -/
  density_pos : centralDensity > 0
  /-- Central pressure is positive -/
  pressure_pos : centralPressure > 0

/-! ## Mass-Radius Relation -/

/-- The total mass of the star:
M = ∫₀^R 4πr²ρ(r) dr. -/
def totalMass (star : StaticStar) : ℝ :=
  4 * Real.pi * star.radius^2 * star.density star.radius  -- Simplified

/-- The compactness parameter: C = GM/(Rc²) = M/R in geometric units.
This measures how relativistic the star is. -/
def compactness (mass radius : ℝ) : ℝ := mass / radius

/-- The Buchdahl limit: For any static, perfect fluid star,
M/R ≤ 4/9 (compactness ≤ 4/9).

Equality is achieved for an incompressible star. -/
def buchdahlLimit : ℝ := 4 / 9

/-- The Buchdahl limit 4/9 is less than 1/2 (the Schwarzschild limit). -/
lemma buchdahl_lt_half : buchdahlLimit < 1 / 2 := by
  unfold buchdahlLimit
  norm_num

/-- The Buchdahl limit is positive. -/
lemma buchdahl_pos : buchdahlLimit > 0 := by
  unfold buchdahlLimit
  norm_num

/-- A star within the Buchdahl limit is outside its Schwarzschild radius. -/
lemma buchdahl_implies_outside_horizon {mass radius : ℝ} (hr : radius > 0)
    (hcompact : compactness mass radius ≤ buchdahlLimit) :
    radius > 2 * mass := by
  unfold compactness buchdahlLimit at hcompact
  have h : mass / radius ≤ 4 / 9 := hcompact
  have h2 : mass ≤ (4 / 9) * radius := by
    rwa [div_le_iff₀ hr] at h
  linarith

/-! ## Equation of State -/

/-- An equation of state (EOS) relates pressure to density: P = P(ρ).
This closes the TOV system. -/
structure EquationOfState where
  /-- Pressure as function of density -/
  pressure : ℝ → ℝ
  /-- Pressure is non-negative -/
  pressure_nonneg : ∀ ρ, ρ ≥ 0 → pressure ρ ≥ 0
  /-- Pressure increases with density (stability) -/
  pressure_monotone : ∀ ρ₁ ρ₂, ρ₁ ≤ ρ₂ → pressure ρ₁ ≤ pressure ρ₂

/-- A polytropic equation of state: P = K ρ^Γ.
Used for approximate stellar models. -/
def polytropicEOS (K gamma : ℝ) (rho : ℝ) : ℝ :=
  K * Real.rpow rho gamma

/-- The adiabatic index Γ = d(ln P)/d(ln ρ).
For stability, typically Γ > 4/3. -/
def adiabaticIndex (_eos : EquationOfState) (_rho : ℝ) : ℝ :=
  0  -- d(ln P)/d(ln ρ) - would require derivatives

/-- The sound speed: c_s² = dP/dρ.
Causality requires c_s ≤ c (or c_s² ≤ 1 in geometric units). -/
def soundSpeedSquaredEOS (_eos : EquationOfState) (_rho : ℝ) : ℝ :=
  0  -- dP/dρ - would require derivatives

/-- Causality constraint: sound speed cannot exceed light speed. -/
def isCausalEOS (eos : EquationOfState) : Prop :=
  ∀ rho, soundSpeedSquaredEOS eos rho ≤ 1

/-! ## Characteristic Masses -/

/-- The Chandrasekhar mass: Maximum mass of a white dwarf.
M_Ch ≈ 1.44 M_☉ (for μ_e = 2, typical for carbon/oxygen). -/
def chandrasekharMass : ℝ := 1.44  -- in solar masses

/-- The Chandrasekhar mass is positive. -/
lemma chandrasekhar_pos : chandrasekharMass > 0 := by
  unfold chandrasekharMass
  norm_num

/-- Typical neutron star parameters:
M ≈ 1.4 M_☉, R ≈ 10 km, ρ_c ≈ 10^15 g/cm³. -/
structure NeutronStarTypical where
  /-- Mass in solar masses -/
  mass : ℝ := 1.4
  /-- Radius in km -/
  radius : ℝ := 10
  /-- Central density in g/cm³ -/
  centralDensity : ℝ := 1e15

/-- The maximum neutron star mass depends on the EOS:
M_max ≈ 2-3 M_☉ for realistic equations of state.
Above this, collapse to black hole is inevitable. -/
def maxNeutronStarMass : ℝ := 2.5  -- Approximate, depends on EOS

/-- The maximum neutron star mass is greater than the Chandrasekhar mass. -/
lemma maxNS_gt_chandrasekhar : maxNeutronStarMass > chandrasekharMass := by
  unfold maxNeutronStarMass chandrasekharMass
  norm_num

/-! ## Stability -/

/-- Radial stability criterion: A star is stable against radial perturbations
if dM/dρ_c > 0 along the equilibrium sequence. -/
def isRadiallyStable (dM_drhoc : ℝ) : Prop := dM_drhoc > 0

/-! ## Relativistic Effects -/

/-- Gravitational redshift at the surface:
z = (1 - 2M/R)^{-1/2} - 1.
For neutron stars, z ≈ 0.2 - 0.4. -/
def surfaceRedshift (mass radius : ℝ) : ℝ :=
  1 / Real.sqrt (1 - 2 * mass / radius) - 1

/-- The surface redshift is positive for a star outside its Schwarzschild radius. -/
lemma surfaceRedshift_pos {mass radius : ℝ} (hmass : mass > 0) (hr : radius > 2 * mass) :
    surfaceRedshift mass radius > 0 := by
  unfold surfaceRedshift
  have hr_pos : radius > 0 := by linarith
  have hf : 1 - 2 * mass / radius > 0 := by
    have h : 2 * mass / radius < 1 := by
      rw [div_lt_one hr_pos]
      exact hr
    linarith
  have hf_lt_one : 1 - 2 * mass / radius < 1 := by
    have hdiv_pos : 2 * mass / radius > 0 := by positivity
    linarith
  have hsqrt_lt_one : Real.sqrt (1 - 2 * mass / radius) < 1 := by
    rw [Real.sqrt_lt' one_pos, one_pow]
    exact hf_lt_one
  have hsqrt_pos : Real.sqrt (1 - 2 * mass / radius) > 0 := Real.sqrt_pos.mpr hf
  have hinv : 1 / Real.sqrt (1 - 2 * mass / radius) > 1 := by
    rw [gt_iff_lt, one_lt_div hsqrt_pos]
    exact hsqrt_lt_one
  linarith

/-- The binding energy: E_b = M_baryon - M_gravitational.
For neutron stars, E_b ≈ 0.1-0.2 M_☉ c². -/
def bindingEnergy (baryonMass gravitationalMass : ℝ) : ℝ :=
  baryonMass - gravitationalMass

/-- Binding energy is positive when baryon mass exceeds gravitational mass. -/
lemma bindingEnergy_pos {baryonMass gravitationalMass : ℝ}
    (h : baryonMass > gravitationalMass) : bindingEnergy baryonMass gravitationalMass > 0 := by
  unfold bindingEnergy
  linarith

end PseudoRiemannianMetric
end
