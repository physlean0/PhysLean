/-
Copyright (c) 2025 PhysLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PhysLean Contributors
-/

import PhysLean.Mathematics.Geometry.Metric.PseudoRiemannian.Einstein

/-!
# de Sitter and Anti-de Sitter Spacetimes

This file formalizes de Sitter (dS) and anti-de Sitter (AdS) spacetimes,
which are the maximally symmetric solutions to Einstein's equations with
positive and negative cosmological constants, respectively.

## Main Definitions

* `DeSitterData`: Parameters for de Sitter spacetime
* `AntiDeSitterData`: Parameters for anti-de Sitter spacetime
* `deSitterStaticMetricFunction`: The de Sitter metric function in static coordinates
* `adSGlobalMetricFunction`: The anti-de Sitter metric function

## Physical Interpretation

de Sitter (Λ > 0):
- Describes an exponentially expanding universe
- Relevant for inflation and dark energy
- Has a cosmological horizon for each observer
- The far future of our universe (if Λ = const)

Anti-de Sitter (Λ < 0):
- Has negative curvature (hyperbolic geometry)
- Central to AdS/CFT correspondence
- Has a timelike boundary at spatial infinity
- Does not describe our universe but crucial for theory

Both spacetimes are maximally symmetric with 10 Killing vectors, the maximum
for a 4D spacetime (same as Minkowski space).

## References

* de Sitter, "On Einstein's Theory of Gravitation" (1917)
* Misner, Thorne, Wheeler, "Gravitation" (1973), Chapter 27
* Hawking & Ellis, "The Large Scale Structure of Space-Time" (1973)
* Maldacena, "The Large N Limit of Superconformal Field Theories" (1997)
-/

noncomputable section

namespace PseudoRiemannianMetric

/-! ## de Sitter Spacetime -/

/-- Data specifying a de Sitter spacetime.
de Sitter is determined by a single parameter: the cosmological constant Λ > 0
or equivalently the Hubble radius ℓ = √(3/Λ). -/
structure DeSitterData where
  /-- The cosmological constant Λ -/
  cosmologicalConstant : ℝ
  /-- Λ is positive for de Sitter -/
  lambda_pos : cosmologicalConstant > 0

/-- The de Sitter radius (Hubble radius): ℓ = √(3/Λ). -/
def DeSitterData.radius (dS : DeSitterData) : ℝ :=
  Real.sqrt (3 / dS.cosmologicalConstant)

/-- The de Sitter radius is positive. -/
lemma DeSitterData.radius_pos (dS : DeSitterData) : dS.radius > 0 := by
  unfold DeSitterData.radius
  apply Real.sqrt_pos_of_pos
  apply div_pos
  · norm_num
  · exact dS.lambda_pos

/-- The Hubble parameter for de Sitter: H = 1/ℓ = √(Λ/3). -/
def DeSitterData.hubbleParameter (dS : DeSitterData) : ℝ :=
  Real.sqrt (dS.cosmologicalConstant / 3)

/-- The Hubble parameter is positive. -/
lemma DeSitterData.hubble_pos (dS : DeSitterData) : dS.hubbleParameter > 0 := by
  unfold DeSitterData.hubbleParameter
  apply Real.sqrt_pos_of_pos
  apply div_pos dS.lambda_pos
  norm_num

/-- de Sitter in static coordinates (valid inside cosmological horizon):
ds² = -(1 - r²/ℓ²)dt² + (1 - r²/ℓ²)⁻¹dr² + r²dΩ²

The cosmological horizon is at r = ℓ. -/
def deSitterStaticMetricFunction (dS : DeSitterData) (r : ℝ) : ℝ :=
  1 - r^2 / dS.radius^2

/-- The metric function is positive inside the horizon (r < ℓ). -/
lemma deSitter_metric_pos_inside {dS : DeSitterData} {r : ℝ}
    (hr_pos : r ≥ 0) (hr : r < dS.radius) :
    deSitterStaticMetricFunction dS r > 0 := by
  unfold deSitterStaticMetricFunction
  have h1 : dS.radius > 0 := dS.radius_pos
  have h2 : r^2 < dS.radius^2 := sq_lt_sq' (by linarith) hr
  have h3 : r^2 / dS.radius^2 < 1 := by
    rw [div_lt_one (sq_pos_of_pos h1)]
    exact h2
  linarith

/-- The cosmological horizon radius in de Sitter: r_H = ℓ. -/
def DeSitterData.horizonRadius (dS : DeSitterData) : ℝ := dS.radius

/-- At the horizon, the metric function vanishes. -/
lemma deSitter_metric_zero_at_horizon (dS : DeSitterData) :
    deSitterStaticMetricFunction dS dS.horizonRadius = 0 := by
  simp only [deSitterStaticMetricFunction, DeSitterData.horizonRadius]
  have h : dS.radius ≠ 0 := ne_of_gt dS.radius_pos
  have h2 : dS.radius^2 ≠ 0 := pow_ne_zero 2 h
  field_simp [h2]
  norm_num

/-- de Sitter in flat slicing (FLRW form):
ds² = -dt² + e^{2Ht}(dx² + dy² + dz²)

This covers the full de Sitter manifold. -/
def deSitterFlatMetricScaleFactor (dS : DeSitterData) (t : ℝ) : ℝ :=
  Real.exp (dS.hubbleParameter * t)

/-- The scale factor is always positive. -/
lemma deSitter_scale_factor_pos (dS : DeSitterData) (t : ℝ) :
    deSitterFlatMetricScaleFactor dS t > 0 := by
  unfold deSitterFlatMetricScaleFactor
  exact Real.exp_pos _

/-- de Sitter in global coordinates (covers full manifold):
ds² = -dτ² + ℓ²cosh²(τ/ℓ)dΩ₃²

where dΩ₃² is the metric on the 3-sphere. -/
def deSitterGlobalScaleFactor (dS : DeSitterData) (tau : ℝ) : ℝ :=
  dS.radius * Real.cosh (tau / dS.radius)

/-- The global scale factor is always positive. -/
lemma deSitter_global_scale_pos (dS : DeSitterData) (tau : ℝ) :
    deSitterGlobalScaleFactor dS tau > 0 := by
  unfold deSitterGlobalScaleFactor
  apply mul_pos dS.radius_pos
  exact Real.cosh_pos _

/-! ## de Sitter Properties -/

/-- The Ricci scalar of de Sitter: R = 4Λ = 12/ℓ². -/
def DeSitterData.ricciScalar (dS : DeSitterData) : ℝ :=
  4 * dS.cosmologicalConstant

/-- The Ricci scalar is positive for de Sitter. -/
lemma DeSitterData.ricci_pos (dS : DeSitterData) : dS.ricciScalar > 0 := by
  unfold DeSitterData.ricciScalar
  linarith [dS.lambda_pos]

/-- The number of Killing vectors in de Sitter (maximally symmetric). -/
def deSitterKillingCount : ℕ := 10

/-! ## de Sitter Thermodynamics -/

/-- The de Sitter horizon has a temperature (Gibbons-Hawking):
T = H/(2π) = 1/(2πℓ). -/
def DeSitterData.temperature (dS : DeSitterData) : ℝ :=
  dS.hubbleParameter / (2 * Real.pi)

/-- The temperature is positive. -/
lemma DeSitterData.temperature_pos (dS : DeSitterData) : dS.temperature > 0 := by
  unfold DeSitterData.temperature
  apply div_pos dS.hubble_pos
  apply mul_pos; norm_num; exact Real.pi_pos

/-- The de Sitter entropy is proportional to horizon area:
S = A/(4) = πℓ² (in Planck units). -/
def DeSitterData.entropy (dS : DeSitterData) : ℝ :=
  Real.pi * dS.radius^2

/-- The entropy is positive. -/
lemma DeSitterData.entropy_pos (dS : DeSitterData) : dS.entropy > 0 := by
  unfold DeSitterData.entropy
  apply mul_pos Real.pi_pos
  exact sq_pos_of_pos dS.radius_pos

/-! ## Anti-de Sitter Spacetime -/

/-- Data specifying an anti-de Sitter spacetime.
AdS has negative cosmological constant Λ < 0. -/
structure AntiDeSitterData where
  /-- The cosmological constant Λ -/
  cosmologicalConstant : ℝ
  /-- Λ is negative for anti-de Sitter -/
  lambda_neg : cosmologicalConstant < 0

/-- The AdS radius: ℓ = √(-3/Λ). -/
def AntiDeSitterData.radius (adS : AntiDeSitterData) : ℝ :=
  Real.sqrt (-3 / adS.cosmologicalConstant)

/-- The AdS radius is positive. -/
lemma AntiDeSitterData.radius_pos (adS : AntiDeSitterData) : adS.radius > 0 := by
  unfold AntiDeSitterData.radius
  apply Real.sqrt_pos_of_pos
  apply div_pos_of_neg_of_neg
  · norm_num
  · exact adS.lambda_neg

/-- Anti-de Sitter in global coordinates:
ds² = -(1 + r²/ℓ²)dt² + (1 + r²/ℓ²)⁻¹dr² + r²dΩ²

Note: No horizon, but r → ∞ is at finite conformal distance. -/
def adSGlobalMetricFunction (adS : AntiDeSitterData) (r : ℝ) : ℝ :=
  1 + r^2 / adS.radius^2

/-- The AdS metric function is always > 1 for r ≠ 0. -/
lemma adS_metric_gt_one {adS : AntiDeSitterData} {r : ℝ} (hr : r ≠ 0) :
    adSGlobalMetricFunction adS r > 1 := by
  unfold adSGlobalMetricFunction
  have h1 : adS.radius > 0 := adS.radius_pos
  have h2 : r^2 > 0 := sq_pos_of_ne_zero hr
  have h3 : r^2 / adS.radius^2 > 0 := div_pos h2 (sq_pos_of_pos h1)
  linarith

/-- The AdS metric function is always positive. -/
lemma adS_metric_pos (adS : AntiDeSitterData) (r : ℝ) :
    adSGlobalMetricFunction adS r > 0 := by
  unfold adSGlobalMetricFunction
  have h1 : adS.radius > 0 := adS.radius_pos
  have h2 : r^2 / adS.radius^2 ≥ 0 := div_nonneg (sq_nonneg r) (sq_nonneg adS.radius)
  linarith

/-- AdS in Poincaré coordinates (covers half of AdS):
ds² = (ℓ²/z²)(-dt² + dx² + dy² + dz²)

The boundary is at z = 0. -/
def adSPoincareConformalFactor (adS : AntiDeSitterData) (z : ℝ) : ℝ :=
  adS.radius^2 / z^2

/-- The Poincaré conformal factor is positive for z ≠ 0. -/
lemma adS_poincare_pos {adS : AntiDeSitterData} {z : ℝ} (hz : z ≠ 0) :
    adSPoincareConformalFactor adS z > 0 := by
  unfold adSPoincareConformalFactor
  apply div_pos
  · exact sq_pos_of_pos adS.radius_pos
  · exact sq_pos_of_ne_zero hz

/-! ## Anti-de Sitter Properties -/

/-- The Ricci scalar of AdS: R = -12/ℓ² = 4Λ. -/
def AntiDeSitterData.ricciScalar (adS : AntiDeSitterData) : ℝ :=
  4 * adS.cosmologicalConstant

/-- The Ricci scalar is negative for AdS. -/
lemma AntiDeSitterData.ricci_neg (adS : AntiDeSitterData) : adS.ricciScalar < 0 := by
  unfold AntiDeSitterData.ricciScalar
  linarith [adS.lambda_neg]

/-- The number of Killing vectors in AdS (maximally symmetric). -/
def adSKillingCount : ℕ := 10

/-! ## Schwarzschild-de Sitter and Schwarzschild-AdS -/

/-- Schwarzschild-de Sitter: A black hole in de Sitter background.
f(r) = 1 - 2M/r - r²/ℓ² (can have 2 horizons). -/
def schwarzschildDeSitterMetricFunction (mass : ℝ) (dS : DeSitterData) (r : ℝ) : ℝ :=
  1 - 2 * mass / r - r^2 / dS.radius^2

/-- Schwarzschild-AdS: A black hole in AdS background.
f(r) = 1 - 2M/r + r²/ℓ² (always has an event horizon for M > 0). -/
def schwarzschildAdSMetricFunction (mass : ℝ) (adS : AntiDeSitterData) (r : ℝ) : ℝ :=
  1 - 2 * mass / r + r^2 / adS.radius^2

/-- For large r, Schwarzschild-dS is dominated by the cosmological term. -/
lemma schwarzschild_dS_large_r_behavior (mass : ℝ) (dS : DeSitterData) (r : ℝ)
    (hr : r > 0) :
    schwarzschildDeSitterMetricFunction mass dS r =
    1 - 2 * mass / r - r^2 / dS.radius^2 := rfl

/-- For large r, Schwarzschild-AdS grows without bound. -/
lemma schwarzschild_adS_large_r_behavior (mass : ℝ) (adS : AntiDeSitterData) (r : ℝ)
    (hr : r > 0) :
    schwarzschildAdSMetricFunction mass adS r =
    1 - 2 * mass / r + r^2 / adS.radius^2 := rfl

/-! ## Comparison of Maximally Symmetric Spacetimes -/

/-- Data for comparing maximally symmetric spacetimes. -/
structure MaximallySymmetricData where
  /-- Cosmological constant Λ -/
  lambda : ℝ
  /-- Scalar curvature R = 4Λ -/
  scalar_curvature : ℝ := 4 * lambda
  /-- All have 10 Killing vectors -/
  killing_vectors : ℕ := 10

/-- Minkowski spacetime data (Λ = 0). -/
def minkowskiData : MaximallySymmetricData where
  lambda := 0

/-- de Sitter from DeSitterData. -/
def deSitterMaxSym (dS : DeSitterData) : MaximallySymmetricData where
  lambda := dS.cosmologicalConstant

/-- AdS from AntiDeSitterData. -/
def adSMaxSym (adS : AntiDeSitterData) : MaximallySymmetricData where
  lambda := adS.cosmologicalConstant

end PseudoRiemannianMetric
end
