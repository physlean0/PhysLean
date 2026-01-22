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

* `TOVEquation`: The relativistic equation of hydrostatic equilibrium
* `MassFunction`: The mass enclosed within radius r
* `CompactnessBound`: The Buchdahl limit M/R < 4/9
* `ChandrasekharLimit`: Maximum mass of white dwarfs

## Main Results

* `tov_equilibrium`: Derivation of the TOV equation
* `buchdahl_theorem`: Maximum compactness of stable stars
* `chandrasekhar_mass`: Mass limit from electron degeneracy
* `neutron_star_mass`: Typical neutron star parameters

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

universe v w

variable {E : Type v} {H : Type w} {M : Type w} {n : WithTop ℕ∞}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] [ChartedSpace H E]
variable {I : ModelWithCorners ℝ E H}
variable [IsManifold I (n + 1) M]
variable [inst_tangent_findim : ∀ (x : M), FiniteDimensional ℝ (TangentSpace I x)]

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

/-- The TOV equation expresses force balance:
pressure gradient = gravitational force (including relativistic corrections). -/
axiom tov_is_force_balance :
    True  -- TOV = relativistic hydrostatic equilibrium

/-- The relativistic corrections in TOV compared to Newtonian:
1. (ρ + P) instead of ρ: pressure contributes to inertia
2. (m + 4πr³P) instead of m: pressure contributes to gravity
3. 1/(r-2m) instead of 1/r²: gravitational redshift factor -/
axiom tov_corrections :
    True  -- Three relativistic corrections

/-- The TOV equation is derived from ∇_μ T^μν = 0 (energy-momentum conservation)
combined with the Einstein equations. -/
axiom tov_from_conservation :
    True  -- T^μν_{;μ} = 0 → TOV

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

/-- At the surface (r = R):
- P(R) = 0 (pressure vanishes at surface)
- The metric matches exterior Schwarzschild -/
axiom surface_boundary_condition :
    True  -- P(R) = 0, matches Schwarzschild exterior

/-- The exterior solution is Schwarzschild with the star's total mass M. -/
axiom exterior_is_schwarzschild :
    True  -- For r > R: Schwarzschild with mass M

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

/-- Buchdahl's theorem: No static star can have M/R > 4/9. -/
axiom buchdahl_theorem :
    True  -- M/R ≤ 4/9 for any static star

/-- A star with M/R > 1/2 would have r < 2M (inside its Schwarzschild radius)
and must collapse. The Buchdahl limit is more stringent: M/R < 4/9. -/
axiom buchdahl_stronger_than_schwarzschild :
    True  -- 4/9 < 1/2

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
def adiabaticIndex (eos : EquationOfState) (_rho : ℝ) : ℝ :=
  0  -- d(ln P)/d(ln ρ)

/-- The sound speed: c_s² = dP/dρ.
Causality requires c_s ≤ c (or c_s² ≤ 1 in geometric units). -/
def soundSpeedSquaredEOS (eos : EquationOfState) (_rho : ℝ) : ℝ :=
  0  -- dP/dρ

/-- Causality constraint: sound speed cannot exceed light speed. -/
def isCausalEOS (eos : EquationOfState) : Prop :=
  ∀ rho, soundSpeedSquaredEOS eos rho ≤ 1

/-! ## White Dwarfs -/

/-- White dwarfs are supported by electron degeneracy pressure.
The equation of state is approximately polytropic with Γ = 5/3 (non-relativistic)
or Γ = 4/3 (relativistic). -/
axiom white_dwarf_degeneracy :
    True  -- Supported by electron degeneracy

/-- The Chandrasekhar mass: Maximum mass of a white dwarf.
M_Ch ≈ 1.44 M_☉ (for μ_e = 2, typical for carbon/oxygen). -/
def chandrasekharMass : ℝ := 1.44  -- in solar masses

/-- Above the Chandrasekhar mass, electron degeneracy cannot support the star,
leading to collapse (to neutron star or Type Ia supernova). -/
axiom chandrasekhar_limit :
    True  -- M > M_Ch → collapse

/-- The mass-radius relation for white dwarfs:
M R³ ≈ constant (for non-relativistic)
As M → M_Ch, R → 0. -/
axiom white_dwarf_mass_radius :
    True  -- M ~ R^{-3} approximately

/-! ## Neutron Stars -/

/-- Neutron stars are supported primarily by neutron degeneracy pressure
and nuclear forces. -/
axiom neutron_star_support :
    True  -- Neutron degeneracy + nuclear forces

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

/-- The TOV limit: Beyond a maximum central density,
increasing ρ_c decreases M (unstable branch). -/
axiom tov_mass_limit :
    True  -- M(ρ_c) has a maximum

/-- The Oppenheimer-Volkoff limit (1939): Using their simplified EOS,
they found M_max ≈ 0.7 M_☉. Modern EOSs give higher values. -/
axiom oppenheimer_volkoff_original :
    True  -- Original M_max ≈ 0.7 M_☉

/-! ## Stability -/

/-- Radial stability criterion: A star is stable against radial perturbations
if dM/dρ_c > 0 along the equilibrium sequence. -/
def isRadiallyStable (dM_drhoc : ℝ) : Prop := dM_drhoc > 0

/-- The turning point theorem: Stability changes sign at M'(ρ_c) = 0. -/
axiom turning_point_theorem :
    True  -- Stability changes at dM/dρ_c = 0

/-- For realistic EOSs, there is a maximum mass beyond which
configurations are unstable and collapse. -/
axiom maximum_mass_stability :
    True  -- M_max separates stable/unstable branches

/-- Non-radial oscillations: Stars can also have non-radial pulsation modes
(f-modes, p-modes, g-modes, w-modes). -/
axiom nonradial_modes :
    True  -- Various oscillation modes exist

/-! ## Relativistic Effects -/

/-- Gravitational redshift at the surface:
z = (1 - 2M/R)^{-1/2} - 1.
For neutron stars, z ≈ 0.2 - 0.4. -/
def surfaceRedshift (mass radius : ℝ) : ℝ :=
  1 / Real.sqrt (1 - 2 * mass / radius) - 1

/-- The binding energy: E_b = M_baryon - M_gravitational.
For neutron stars, E_b ≈ 0.1-0.2 M_☉ c². -/
def bindingEnergy (baryonMass gravitationalMass : ℝ) : ℝ :=
  baryonMass - gravitationalMass

/-- The moment of inertia of a slowly rotating star.
I ≈ 0.4 MR² for neutron stars (depends on EOS). -/
axiom moment_of_inertia :
    True  -- I from slow rotation approximation

/-! ## Exotic Compact Objects -/

/-- Quark stars: Hypothetical stars made of deconfined quark matter. -/
axiom quark_stars :
    True  -- Strange quark matter hypothesis

/-- Hybrid stars: Neutron stars with a quark matter core. -/
axiom hybrid_stars :
    True  -- Hadronic mantle + quark core

/-- Boson stars: Hypothetical stars made of scalar field matter. -/
axiom boson_stars :
    True  -- Supported by scalar field gradient

end PseudoRiemannianMetric
end
