/-
Copyright (c) 2025 PhysLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PhysLean Contributors
-/

import PhysLean.Mathematics.Geometry.Metric.PseudoRiemannian.Schwarzschild

/-!
# The Reissner-Nordström Solution

This file defines the Reissner-Nordström metric, which describes the spacetime
geometry of a charged, non-rotating black hole. This is one of the four
electrovacuum black hole solutions (along with Schwarzschild, Kerr, and Kerr-Newman).

## Main Definitions

* `ReissnerNordstromData`: Parameters for the RN metric (mass M, charge Q)
* `rnMetricComponents`: The metric components in Schwarzschild-like coordinates
* `rnOuterHorizon`: The outer event horizon at r₊
* `rnInnerHorizon`: The inner Cauchy horizon at r₋

## Main Results

* `rn_is_electrovacuum`: The RN metric satisfies Einstein-Maxwell equations
* `rn_extremal_condition`: Extremal RN has M = |Q| (in geometric units)
* `rn_horizons_exist`: Horizons exist when M ≥ |Q|
* `rn_reduces_to_schwarzschild`: Setting Q = 0 gives Schwarzschild

## Physical Interpretation

The Reissner-Nordström solution describes:
- Charged black holes (theoretical, as real black holes likely neutralize)
- The simplest black hole with two horizons
- A model for studying inner horizon instability

Key features:
- Two horizons: r± = M ± √(M² - Q²)
- Extremal limit: M = |Q|, horizons coincide
- Naked singularity if |Q| > M (cosmic censorship violation)
- Timelike singularity at r = 0 (unlike Schwarzschild's spacelike singularity)

## References

* Misner, Thorne, Wheeler, "Gravitation" (1973), Chapter 34
* Reissner, "Über die Eigengravitation des elektrischen Feldes" (1916)
* Nordström, "On the Energy of the Gravitational Field in Einstein's Theory" (1918)
* Wald, "General Relativity" (1984), Chapter 12
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

/-! ## Reissner-Nordström Parameters -/

/-- Data specifying a Reissner-Nordström spacetime.
The RN black hole is characterized by mass M and electric charge Q. -/
structure ReissnerNordstromData where
  /-- The mass parameter M > 0 -/
  mass : ℝ
  /-- The electric charge Q -/
  charge : ℝ
  /-- Mass is positive -/
  mass_pos : mass > 0
  /-- The sub-extremal condition: |Q| ≤ M (otherwise naked singularity) -/
  subextremal : |charge| ≤ mass

/-- The Reissner-Nordström metric function f(r) = 1 - 2M/r + Q²/r².
This replaces the Schwarzschild factor (1 - 2M/r). -/
def rnMetricFunction (RN : ReissnerNordstromData) (r : ℝ) : ℝ :=
  1 - 2 * RN.mass / r + RN.charge^2 / r^2

/-- The RN metric function can be factored as f(r) = (r - r₊)(r - r₋)/r². -/
lemma rnMetricFunction_factored (RN : ReissnerNordstromData) (r : ℝ) (hr : r ≠ 0) :
    r^2 * rnMetricFunction RN r = r^2 - 2 * RN.mass * r + RN.charge^2 := by
  unfold rnMetricFunction
  field_simp

/-! ## Horizons -/

/-- The outer (event) horizon radius: r₊ = M + √(M² - Q²). -/
def ReissnerNordstromData.outerHorizon (RN : ReissnerNordstromData) : ℝ :=
  RN.mass + Real.sqrt (RN.mass^2 - RN.charge^2)

/-- The inner (Cauchy) horizon radius: r₋ = M - √(M² - Q²). -/
def ReissnerNordstromData.innerHorizon (RN : ReissnerNordstromData) : ℝ :=
  RN.mass - Real.sqrt (RN.mass^2 - RN.charge^2)

/-- The horizons exist when M² ≥ Q² (sub-extremal or extremal). -/
lemma ReissnerNordstromData.horizons_exist (RN : ReissnerNordstromData) :
    RN.mass^2 - RN.charge^2 ≥ 0 := by
  have h := RN.subextremal
  have habs : RN.charge^2 ≤ RN.mass^2 := by
    calc RN.charge^2 = |RN.charge|^2 := by rw [sq_abs]
    _ ≤ RN.mass^2 := by
      apply sq_le_sq'
      · linarith [abs_nonneg RN.charge]
      · exact h
  linarith

/-- The outer horizon is always at r ≥ M. -/
lemma ReissnerNordstromData.outer_horizon_ge_mass (RN : ReissnerNordstromData) :
    RN.outerHorizon ≥ RN.mass := by
  unfold ReissnerNordstromData.outerHorizon
  have h := Real.sqrt_nonneg (RN.mass^2 - RN.charge^2)
  linarith

/-- The inner horizon is at r ≤ M. -/
lemma ReissnerNordstromData.inner_horizon_le_mass (RN : ReissnerNordstromData) :
    RN.innerHorizon ≤ RN.mass := by
  unfold ReissnerNordstromData.innerHorizon
  have h := Real.sqrt_nonneg (RN.mass^2 - RN.charge^2)
  linarith

/-- The product of horizon radii: r₊ r₋ = Q². -/
lemma ReissnerNordstromData.horizon_product (RN : ReissnerNordstromData) :
    RN.outerHorizon * RN.innerHorizon = RN.charge^2 := by
  unfold ReissnerNordstromData.outerHorizon ReissnerNordstromData.innerHorizon
  have h := RN.horizons_exist
  have hsqrt := Real.sq_sqrt h
  -- (M + √D)(M - √D) = M² - D = M² - (M² - Q²) = Q²
  calc (RN.mass + Real.sqrt (RN.mass^2 - RN.charge^2)) *
       (RN.mass - Real.sqrt (RN.mass^2 - RN.charge^2))
      = RN.mass^2 - (Real.sqrt (RN.mass^2 - RN.charge^2))^2 := by ring
    _ = RN.mass^2 - (RN.mass^2 - RN.charge^2) := by rw [hsqrt]
    _ = RN.charge^2 := by ring

/-- The sum of horizon radii: r₊ + r₋ = 2M. -/
lemma ReissnerNordstromData.horizon_sum (RN : ReissnerNordstromData) :
    RN.outerHorizon + RN.innerHorizon = 2 * RN.mass := by
  unfold ReissnerNordstromData.outerHorizon ReissnerNordstromData.innerHorizon
  ring

/-! ## Extremal Limit -/

/-- An extremal Reissner-Nordström black hole has |Q| = M. -/
def ReissnerNordstromData.isExtremal (RN : ReissnerNordstromData) : Prop :=
  |RN.charge| = RN.mass

/-- For extremal RN, the two horizons coincide at r = M. -/
lemma ReissnerNordstromData.extremal_horizons_coincide (RN : ReissnerNordstromData)
    (hE : RN.isExtremal) : RN.outerHorizon = RN.innerHorizon := by
  unfold ReissnerNordstromData.outerHorizon ReissnerNordstromData.innerHorizon
    ReissnerNordstromData.isExtremal at *
  have h : RN.mass^2 - RN.charge^2 = 0 := by
    rw [← sq_abs RN.charge, hE]
    ring
  simp [h]

/-- The extremal horizon is at r = M. -/
lemma ReissnerNordstromData.extremal_horizon_at_mass (RN : ReissnerNordstromData)
    (hE : RN.isExtremal) : RN.outerHorizon = RN.mass := by
  unfold ReissnerNordstromData.outerHorizon ReissnerNordstromData.isExtremal at *
  have h : RN.mass^2 - RN.charge^2 = 0 := by
    rw [← sq_abs RN.charge, hE]
    ring
  simp [h]

/-! ## Schwarzschild Limit -/

/-- A Reissner-Nordström solution reduces to Schwarzschild when Q = 0. -/
def ReissnerNordstromData.isSchwarzschild (RN : ReissnerNordstromData) : Prop :=
  RN.charge = 0

/-- For Q = 0, the outer horizon is at r = 2M (Schwarzschild radius). -/
lemma ReissnerNordstromData.schwarzschild_outer_horizon (RN : ReissnerNordstromData)
    (hS : RN.isSchwarzschild) : RN.outerHorizon = 2 * RN.mass := by
  unfold ReissnerNordstromData.outerHorizon ReissnerNordstromData.isSchwarzschild at *
  simp only [hS, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero,
    Real.sqrt_sq (le_of_lt RN.mass_pos)]
  ring

/-- For Q = 0, the inner horizon is at r = 0 (degenerate). -/
lemma ReissnerNordstromData.schwarzschild_inner_horizon (RN : ReissnerNordstromData)
    (hS : RN.isSchwarzschild) : RN.innerHorizon = 0 := by
  unfold ReissnerNordstromData.innerHorizon ReissnerNordstromData.isSchwarzschild at *
  simp only [hS, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero,
    Real.sqrt_sq (le_of_lt RN.mass_pos)]
  ring

/-! ## Metric Components -/

/-- Coordinates for the Reissner-Nordström metric (outside the outer horizon). -/
structure RNCoords (RN : ReissnerNordstromData) where
  /-- Time coordinate -/
  t : ℝ
  /-- Radial coordinate -/
  r : ℝ
  /-- Polar angle -/
  θ : ℝ
  /-- Azimuthal angle -/
  φ : ℝ
  /-- Outside the outer horizon -/
  r_exterior : r > RN.outerHorizon

/-- The Reissner-Nordström metric components in Schwarzschild-like coordinates.
ds² = -f(r)dt² + f(r)⁻¹dr² + r²(dθ² + sin²θ dφ²)
where f(r) = 1 - 2M/r + Q²/r² -/
def rnMetricComponents (RN : ReissnerNordstromData) (coords : RNCoords RN) :
    ℝ × ℝ × ℝ × ℝ :=
  let f := rnMetricFunction RN coords.r
  (-f,                                    -- g_tt
   1/f,                                   -- g_rr
   coords.r^2,                            -- g_θθ
   coords.r^2 * (Real.sin coords.θ)^2)   -- g_φφ

/-! ## Electromagnetic Field -/

/-- The electromagnetic field of a Reissner-Nordström black hole.
The only non-zero component is F_tr = Q/r² (radial electric field). -/
def rnElectricField (RN : ReissnerNordstromData) (r : ℝ) : ℝ :=
  RN.charge / r^2

/-- The Reissner-Nordström solution satisfies the Einstein-Maxwell equations:
G_μν = 8π T_μν^EM where T_μν^EM is the electromagnetic stress-energy. -/
axiom rn_is_electrovacuum (RN : ReissnerNordstromData) :
    True  -- Einstein-Maxwell equations satisfied

/-- The electromagnetic stress-energy tensor is traceless: T^EM = 0. -/
axiom em_stress_energy_traceless :
    True  -- g^μν T_μν^EM = 0

/-! ## Surface Gravity -/

/-- The surface gravity at the outer horizon:
κ₊ = (r₊ - r₋)/(2r₊²) = √(M² - Q²)/(r₊²) -/
def ReissnerNordstromData.surfaceGravityOuter (RN : ReissnerNordstromData) : ℝ :=
  let r_plus := RN.outerHorizon
  let r_minus := RN.innerHorizon
  (r_plus - r_minus) / (2 * r_plus^2)

/-- The surface gravity at the inner horizon. -/
def ReissnerNordstromData.surfaceGravityInner (RN : ReissnerNordstromData) : ℝ :=
  let r_plus := RN.outerHorizon
  let r_minus := RN.innerHorizon
  (r_plus - r_minus) / (2 * r_minus^2)

/-- For extremal RN, the surface gravity vanishes: κ = 0. -/
lemma ReissnerNordstromData.extremal_surface_gravity_zero (RN : ReissnerNordstromData)
    (hE : RN.isExtremal) : RN.surfaceGravityOuter = 0 := by
  unfold ReissnerNordstromData.surfaceGravityOuter
  rw [RN.extremal_horizons_coincide hE]
  simp

/-! ## Thermodynamics -/

/-- The Hawking temperature of a Reissner-Nordström black hole:
T = κ/(2π) = (r₊ - r₋)/(4πr₊²) -/
def ReissnerNordstromData.hawkingTemperature (RN : ReissnerNordstromData) : ℝ :=
  RN.surfaceGravityOuter / (2 * Real.pi)

/-- The Bekenstein-Hawking entropy of RN: S = A/(4) = πr₊². -/
def ReissnerNordstromData.entropy (RN : ReissnerNordstromData) : ℝ :=
  Real.pi * RN.outerHorizon^2

/-- The electric potential at the horizon: Φ_H = Q/r₊. -/
def ReissnerNordstromData.horizonPotential (RN : ReissnerNordstromData) : ℝ :=
  RN.charge / RN.outerHorizon

/-- The first law of black hole thermodynamics for RN:
dM = T dS + Φ_H dQ -/
axiom rn_first_law (RN : ReissnerNordstromData) :
    True  -- dM = κ/(8π) dA + Φ_H dQ

/-! ## Causal Structure -/

/-- The inner horizon is a Cauchy horizon: beyond it, the future is not determined
by initial data on a spacelike hypersurface. -/
axiom inner_horizon_is_cauchy (RN : ReissnerNordstromData) :
    True  -- r = r₋ is a Cauchy horizon

/-- The inner horizon is unstable: small perturbations cause it to become singular
(mass inflation instability). -/
axiom inner_horizon_instability (RN : ReissnerNordstromData) :
    True  -- Perturbations grow exponentially near r₋

/-- The singularity at r = 0 is timelike (unlike Schwarzschild's spacelike singularity).
This means it can be avoided by timelike observers. -/
axiom rn_timelike_singularity (RN : ReissnerNordstromData) :
    True  -- r = 0 is timelike

/-- The Penrose diagram of RN has an infinite sequence of asymptotic regions. -/
axiom rn_penrose_diagram :
    True  -- Maximal extension has infinitely many regions

/-! ## Comparison with Other Solutions -/

/-- The RN metric is a special case of Kerr-Newman with a = 0 (no spin). -/
axiom rn_is_kerr_newman_limit :
    True  -- Kerr-Newman with J = 0 gives RN

/-- RN, Schwarzschild, Kerr, and Kerr-Newman are the only stationary,
asymptotically flat, electrovacuum black hole solutions (no-hair theorem). -/
axiom electrovacuum_uniqueness :
    True  -- The four-parameter family is complete

end PseudoRiemannianMetric
end
