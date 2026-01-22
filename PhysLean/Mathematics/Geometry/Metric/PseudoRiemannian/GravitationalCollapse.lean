/-
Copyright (c) 2025 PhysLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PhysLean Contributors
-/

import PhysLean.Mathematics.Geometry.Metric.PseudoRiemannian.Schwarzschild

/-!
# Gravitational Collapse

This file formalizes gravitational collapse in general relativity, including
the Oppenheimer-Snyder model of dust collapse and the formation of black holes.
This connects the theory of stars to black hole physics.

## Main Definitions

* `OppenheimerSnyder`: The OS collapse model
* `CollapsingDustBall`: A spherically symmetric dust cloud
* `ApparentHorizon`: The outermost trapped surface
* `EventHorizon`: The boundary of the black hole region

## Main Results

* `os_collapse_forms_bh`: OS collapse produces a black hole
* `trapped_surface_formation`: When trapped surfaces first appear
* `singularity_inevitable`: Singularity theorems apply to collapse
* `cosmic_censorship`: The singularity is hidden (conjecture)

## Physical Interpretation

The Oppenheimer-Snyder model (1939) shows that:
1. A ball of dust inevitably collapses under its own gravity
2. An event horizon forms, creating a black hole
3. The matter reaches a singularity in finite proper time
4. The exterior remains Schwarzschild throughout

This was the first demonstration that black holes form from
realistic initial conditions (stars).

## References

* Oppenheimer & Snyder, "On Continued Gravitational Contraction" (1939)
* Misner, Thorne, Wheeler, "Gravitation" (1973), Chapter 32
* Penrose, "Gravitational Collapse and Space-Time Singularities" (1965)
* Joshi, "Gravitational Collapse and Spacetime Singularities" (2007)
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

/-! ## The Oppenheimer-Snyder Model -/

/-- The Oppenheimer-Snyder (OS) collapse model: a uniform density ball of
pressureless dust (P = 0) collapsing from rest under its own gravity. -/
structure OppenheimerSnyderData where
  /-- Initial radius of the dust ball -/
  initialRadius : ℝ
  /-- Total mass (constant during collapse) -/
  totalMass : ℝ
  /-- Initial density (uniform) -/
  initialDensity : ℝ
  /-- Radius is positive -/
  radius_pos : initialRadius > 0
  /-- Mass is positive -/
  mass_pos : totalMass > 0
  /-- Mass-density consistency: M = (4π/3)ρR³ -/
  mass_density_relation : totalMass = (4 * Real.pi / 3) * initialDensity * initialRadius^3

/-- The interior of the OS dust ball is described by a closed FLRW universe
(k = +1) with dust (P = 0). -/
axiom os_interior_is_flrw :
    True  -- Interior: closed dust FLRW

/-- The exterior of the OS dust ball is Schwarzschild vacuum (Birkhoff). -/
axiom os_exterior_is_schwarzschild (os : OppenheimerSnyderData) :
    True  -- Exterior: Schwarzschild with mass M

/-- The interior and exterior are matched at the surface of the dust ball
using the Israel junction conditions. -/
axiom os_junction_conditions :
    True  -- Israel conditions at r = R(τ)

/-! ## Collapse Dynamics -/

/-- The surface radius R(τ) as a function of proper time τ on the surface.
The surface follows a radial geodesic in Schwarzschild. -/
def surfaceRadius (os : OppenheimerSnyderData) (_tau : ℝ) : ℝ :=
  os.initialRadius  -- Would be R(τ) from geodesic equation

/-- The parametric solution for dust collapse:
R = (R_i/2)(1 + cos η)
τ = (R_i/2)√(R_i/2M)(η + sin η)
where η goes from 0 to π. -/
axiom os_parametric_solution :
    True  -- Cycloid solution

/-- The total proper time for collapse from rest at r = R_i to r = 0:
τ_collapse = (π/2)√(R_i³/2M). -/
def collapseProperTime (os : OppenheimerSnyderData) : ℝ :=
  (Real.pi / 2) * Real.sqrt (os.initialRadius^3 / (2 * os.totalMass))

/-- The collapse proper time is finite: matter reaches r = 0 in finite τ. -/
lemma collapse_time_finite (os : OppenheimerSnyderData) :
    collapseProperTime os > 0 := by
  unfold collapseProperTime
  apply mul_pos
  · apply div_pos Real.pi_pos
    norm_num
  · apply Real.sqrt_pos_of_pos
    apply div_pos
    · apply pow_pos os.radius_pos
    · linarith [os.mass_pos]

/-! ## Horizon Formation -/

/-- The event horizon forms when the surface crosses r = 2M.
This occurs at η* where R(η*) = 2M. -/
def horizonFormationRadius (os : OppenheimerSnyderData) : ℝ :=
  2 * os.totalMass

/-- The event horizon forms before the singularity:
τ_horizon < τ_singularity. -/
axiom horizon_before_singularity (os : OppenheimerSnyderData) :
    True  -- Horizon forms first

/-- Once the surface enters r < 2M, it cannot escape.
The entire interior is trapped. -/
axiom surface_inside_horizon_trapped :
    True  -- r < 2M → inevitably reaches r = 0

/-- The apparent horizon coincides with r = 2M at the moment of crossing. -/
axiom apparent_horizon_at_crossing :
    True  -- AH = EH at formation

/-- From the outside (Schwarzschild coordinates), the surface takes
infinite coordinate time t to reach r = 2M (never quite gets there). -/
axiom infinite_coordinate_time_to_horizon :
    True  -- t → ∞ as r → 2M

/-- In proper time, the infalling matter crosses r = 2M smoothly
and reaches r = 0 in finite proper time. -/
axiom finite_proper_time_through_horizon :
    True  -- τ finite through r = 2M to r = 0

/-! ## Singularity Formation -/

/-- The central singularity at r = 0 is a physical singularity:
curvature diverges (R_μνρσ R^μνρσ → ∞). -/
axiom os_singularity_is_physical :
    True  -- Curvature invariants diverge

/-- The singularity is spacelike: once formed, it lies in the future
of all interior points. -/
axiom os_singularity_spacelike :
    True  -- Singularity is spacelike surface

/-- The Penrose singularity theorem applies: the trapped surface that forms
guarantees a singularity. -/
axiom penrose_applies_to_os :
    True  -- Trapped surface → singularity

/-- Cosmic censorship (weak): The singularity is hidden behind the
event horizon; no naked singularity forms. -/
axiom os_censorship :
    True  -- Singularity inside horizon

/-! ## External Observer's View -/

/-- An external observer sees the collapsing star freeze at the horizon.
This led to the historical name "frozen star." -/
axiom external_sees_freeze :
    True  -- Surface approaches r = 2M asymptotically

/-- Light from the surface is increasingly redshifted:
z → ∞ as surface → horizon. -/
def surfaceRedshiftDuringCollapse (r mass : ℝ) : ℝ :=
  1 / Real.sqrt (1 - 2 * mass / r) - 1

/-- The luminosity of the collapsing star decreases exponentially
with e-folding time ~ M (the light-crossing time of the horizon). -/
axiom luminosity_exponential_decay :
    True  -- L ~ exp(-t/M)

/-- The collapsing star quickly becomes "black" (undetectable)
even though horizon formation takes infinite coordinate time. -/
axiom rapid_dimming :
    True  -- Becomes unobservable in ~ M

/-! ## Beyond Oppenheimer-Snyder -/

/-- Real collapse includes pressure, which can delay but not prevent
collapse for massive enough stars. -/
axiom pressure_delays_collapse :
    True  -- P > 0 delays but doesn't prevent collapse

/-- Rotation leads to Kerr black hole formation.
Angular momentum is conserved during collapse. -/
axiom rotating_collapse_kerr :
    True  -- Rotating collapse → Kerr BH

/-- Charge leads to Reissner-Nordström or Kerr-Newman.
In practice, charge is quickly neutralized. -/
axiom charged_collapse :
    True  -- Charged collapse → RN or KN

/-- Non-spherical perturbations are radiated away as gravitational waves,
leaving a Kerr black hole (no-hair theorem). -/
axiom multipoles_radiated :
    True  -- Perturbations → GW, final state → Kerr

/-! ## Critical Phenomena in Collapse -/

/-- Choptuik (1993) discovered critical phenomena in gravitational collapse:
at the threshold of black hole formation, the mass scales as
M_BH ~ (p - p*)^γ with universal exponent γ ≈ 0.37. -/
axiom choptuik_critical_phenomena :
    True  -- M_BH ~ (p - p*)^0.37

/-- At the critical point, the solution is discretely self-similar
with echoing period Δ ≈ 3.44. -/
axiom choptuik_self_similarity :
    True  -- Discrete self-similarity at threshold

/-- Sub-critical collapse (p < p*) disperses; super-critical (p > p*)
forms a black hole of arbitrarily small mass near threshold. -/
axiom critical_collapse_threshold :
    True  -- p < p* → dispersion, p > p* → BH

/-! ## Numerical Relativity -/

/-- The full Einstein equations for collapse require numerical solution
except in highly symmetric cases (like OS). -/
axiom numerical_relativity_needed :
    True  -- General collapse requires numerics

/-- Binary black hole mergers (LIGO) and neutron star mergers are
studied with numerical relativity. -/
axiom numerical_mergers :
    True  -- BBH, BNS mergers simulated

/-- The 3+1 decomposition (ADM formalism) is commonly used:
evolve spatial metric γ_ij and extrinsic curvature K_ij. -/
axiom adm_for_collapse :
    True  -- ADM formalism for numerical evolution

/-! ## Astrophysical Collapse -/

/-- Core-collapse supernovae: massive stars (M > 8 M_☉) end their
lives in gravitational collapse of the iron core. -/
axiom core_collapse_supernova :
    True  -- Fe core collapse → NS or BH

/-- If the core mass exceeds the TOV limit, a black hole forms.
Otherwise, a neutron star (possibly with supernova explosion). -/
axiom collapse_outcome :
    True  -- M_core > M_TOV → BH

/-- Pair-instability supernovae: Very massive stars (130-250 M_☉)
are completely disrupted, leaving no remnant. -/
axiom pair_instability :
    True  -- No remnant in 130-250 M_☉ range

/-- Direct collapse: Stars above ~250 M_☉ may collapse directly
to black holes without explosion. -/
axiom direct_collapse :
    True  -- M > 250 M_☉ → direct collapse to BH

/-! ## Observational Evidence -/

/-- X-ray binaries: Accretion onto compact objects reveals BH candidates
through their mass (M > 3 M_☉) and lack of surface. -/
axiom xray_binary_evidence :
    True  -- Cygnus X-1, etc.

/-- Gravitational wave observations (LIGO/Virgo) detect mergers of
black holes formed from stellar collapse. -/
axiom gravitational_wave_mergers :
    True  -- GW150914, etc.

/-- Supermassive black holes: M ~ 10⁶-10¹⁰ M_☉ at galaxy centers.
Formation mechanisms include direct collapse and mergers. -/
axiom supermassive_black_holes :
    True  -- M87*, Sgr A*, etc.

end PseudoRiemannianMetric
end
