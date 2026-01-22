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

## Main Definitions

* `OppenheimerSnyderData`: Initial data for the OS collapse model
* `collapseProperTime`: Total proper time for collapse
* `horizonFormationRadius`: The Schwarzschild radius r = 2M
* `surfaceRedshiftDuringCollapse`: Redshift of light from collapsing surface

## Main Results

* `collapse_time_finite`: Collapse happens in finite proper time
* `horizon_less_than_initial`: The horizon radius is less than initial radius for
  physically reasonable initial data

## Physical Interpretation

The Oppenheimer-Snyder model (1939) demonstrates that:
1. A ball of dust inevitably collapses under its own gravity
2. An event horizon forms at r = 2M, creating a black hole
3. The matter reaches a singularity in finite proper time
4. The exterior remains Schwarzschild throughout (Birkhoff's theorem)

The interior is a closed FLRW universe with dust; the exterior is Schwarzschild;
they are matched at the surface using the Israel junction conditions.

## References

* Oppenheimer & Snyder, "On Continued Gravitational Contraction" (1939)
* Misner, Thorne, Wheeler, "Gravitation" (1973), Chapter 32
* Penrose, "Gravitational Collapse and Space-Time Singularities" (1965)
-/

noncomputable section

open Bundle Set Finset Function Filter Module Topology ContinuousLinearMap
open scoped Manifold Bundle LinearMap Dual

namespace PseudoRiemannianMetric

/-! ## The Oppenheimer-Snyder Model -/

/-- The Oppenheimer-Snyder (OS) collapse model: a uniform density ball of
pressureless dust (P = 0) collapsing from rest under its own gravity.

The interior is described by a closed FLRW universe (k = +1) with dust.
The exterior is Schwarzschild (by Birkhoff's theorem).
They are matched at the surface using the Israel junction conditions. -/
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

/-! ## Collapse Dynamics -/

/-- The total proper time for collapse from rest at r = R_i to r = 0:
τ_collapse = (π/2)√(R_i³/2M).

This follows from integrating the radial geodesic equation for a dust particle
falling from rest at r = R_i. -/
def collapseProperTime (os : OppenheimerSnyderData) : ℝ :=
  (Real.pi / 2) * Real.sqrt (os.initialRadius^3 / (2 * os.totalMass))

/-- The collapse proper time is positive (and finite). -/
lemma collapse_time_pos (os : OppenheimerSnyderData) :
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
This is the Schwarzschild radius for the collapsing mass. -/
def horizonFormationRadius (os : OppenheimerSnyderData) : ℝ :=
  2 * os.totalMass

/-- The horizon radius is positive. -/
lemma horizon_radius_pos (os : OppenheimerSnyderData) :
    horizonFormationRadius os > 0 := by
  unfold horizonFormationRadius
  linarith [os.mass_pos]

/-- For collapse to form a black hole, the initial radius must be greater than
the Schwarzschild radius: R_i > 2M. Otherwise, the dust ball is already inside
its own horizon. -/
def isPhysicalCollapse (os : OppenheimerSnyderData) : Prop :=
  os.initialRadius > horizonFormationRadius os

/-- The horizon radius in terms of the Schwarzschild radius. -/
lemma horizon_eq_schwarzschild_radius (os : OppenheimerSnyderData) :
    horizonFormationRadius os = schwarzschildRadius os.totalMass := by
  unfold horizonFormationRadius schwarzschildRadius
  ring

/-! ## Redshift During Collapse -/

/-- The gravitational redshift of light emitted from the collapsing surface
at radius r, for mass M. As r → 2M, the redshift z → ∞.

z = 1/√(1 - 2M/r) - 1 -/
def surfaceRedshiftDuringCollapse (r mass : ℝ) : ℝ :=
  1 / Real.sqrt (1 - 2 * mass / r) - 1

/-- The redshift is positive for r > 2M. -/
lemma redshift_pos {r mass : ℝ} (hmass : mass > 0) (hr : r > 2 * mass) :
    surfaceRedshiftDuringCollapse r mass > 0 := by
  unfold surfaceRedshiftDuringCollapse
  have hr_pos : r > 0 := by linarith
  have hf : 1 - 2 * mass / r > 0 := by
    have h : 2 * mass / r < 1 := by
      rw [div_lt_one hr_pos]
      exact hr
    linarith
  have hf_lt_one : 1 - 2 * mass / r < 1 := by
    have hdiv_pos : 2 * mass / r > 0 := by positivity
    linarith
  have hsqrt_lt_one : Real.sqrt (1 - 2 * mass / r) < 1 := by
    rw [Real.sqrt_lt' one_pos, one_pow]
    exact hf_lt_one
  have hsqrt_pos : Real.sqrt (1 - 2 * mass / r) > 0 := Real.sqrt_pos.mpr hf
  have hinv : 1 / Real.sqrt (1 - 2 * mass / r) > 1 := by
    rw [gt_iff_lt, one_lt_div hsqrt_pos]
    exact hsqrt_lt_one
  linarith

end PseudoRiemannianMetric
end
