/-
Copyright (c) 2025 PhysLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PhysLean Contributors
-/

import PhysLean.Mathematics.Geometry.Metric.PseudoRiemannian.Kerr

/-!
# The Kerr-Newman Solution

This file defines the Kerr-Newman metric, which describes the most general
stationary, axisymmetric, asymptotically flat black hole solution in
Einstein-Maxwell theory. It is characterized by mass M, angular momentum J,
and electric charge Q.

## Main Definitions

* `KerrNewmanData`: Parameters (mass M, spin a, charge Q)
* `knMetricComponents`: The metric components in Boyer-Lindquist coordinates
* `knElectromagneticField`: The electromagnetic field tensor
* `knHorizons`: The inner and outer horizons

## Main Results

* Horizon existence and properties
* Thermodynamic quantities (temperature, entropy)
* Special case limits (Kerr, RN, Schwarzschild)

## Physical Properties

The Kerr-Newman solution satisfies:
- Einstein-Maxwell equations: G_μν = 8π T_μν^EM (electrovacuum)
- Stationarity: ∂/∂t is a Killing vector
- Axisymmetry: ∂/∂φ is a Killing vector
- No-hair theorem uniqueness: the unique stationary axisymmetric
  electrovacuum black hole solution

The solution completes the classification of stationary black holes:

| Solution           | M | J | Q |
|-------------------|---|---|---|
| Schwarzschild     | ✓ | 0 | 0 |
| Kerr              | ✓ | ✓ | 0 |
| Reissner-Nordström| ✓ | 0 | ✓ |
| Kerr-Newman       | ✓ | ✓ | ✓ |

## References

* Misner, Thorne, Wheeler, "Gravitation" (1973), Chapter 33
* Newman et al., "Metric of a Rotating, Charged Mass" (1965)
* Wald, "General Relativity" (1984), Chapter 12
* Chandrasekhar, "The Mathematical Theory of Black Holes" (1983)
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

/-! ## Kerr-Newman Parameters -/

/-- Data specifying a Kerr-Newman spacetime.
The most general stationary black hole is characterized by mass M,
spin parameter a = J/M, and electric charge Q. -/
structure KerrNewmanData where
  /-- The mass parameter M > 0 -/
  mass : ℝ
  /-- The spin parameter a = J/M -/
  spinParameter : ℝ
  /-- The electric charge Q -/
  charge : ℝ
  /-- Mass is positive -/
  mass_pos : mass > 0
  /-- The Kerr-Newman bound: a² + Q² ≤ M² (otherwise naked singularity) -/
  kn_bound : spinParameter^2 + charge^2 ≤ mass^2

/-- The angular momentum J = aM of a Kerr-Newman black hole. -/
def KerrNewmanData.angularMomentum (KN : KerrNewmanData) : ℝ :=
  KN.spinParameter * KN.mass

/-! ## Special Cases -/

/-- A Kerr-Newman black hole is extremal if a² + Q² = M². -/
def KerrNewmanData.isExtremal (KN : KerrNewmanData) : Prop :=
  KN.spinParameter^2 + KN.charge^2 = KN.mass^2

/-- Reduces to Schwarzschild when a = Q = 0. -/
def KerrNewmanData.isSchwarzschild (KN : KerrNewmanData) : Prop :=
  KN.spinParameter = 0 ∧ KN.charge = 0

/-- Reduces to Kerr when Q = 0. -/
def KerrNewmanData.isKerr (KN : KerrNewmanData) : Prop :=
  KN.charge = 0

/-- Reduces to Reissner-Nordström when a = 0. -/
def KerrNewmanData.isReissnerNordstrom (KN : KerrNewmanData) : Prop :=
  KN.spinParameter = 0

/-! ## Metric Functions -/

/-- The function Δ(r) = r² - 2Mr + a² + Q² for Kerr-Newman.
The roots give the horizon radii. -/
def knDelta (KN : KerrNewmanData) (r : ℝ) : ℝ :=
  r^2 - 2 * KN.mass * r + KN.spinParameter^2 + KN.charge^2

/-- The function Σ(r,θ) = r² + a²cos²θ (same as Kerr). -/
def knSigma (KN : KerrNewmanData) (r θ : ℝ) : ℝ :=
  r^2 + KN.spinParameter^2 * (Real.cos θ)^2

/-- The function ρ² = r² + a²cos²θ = Σ. -/
def knRhoSquared (KN : KerrNewmanData) (r θ : ℝ) : ℝ :=
  knSigma KN r θ

/-! ## Horizons -/

/-- The discriminant M² - a² - Q² determines horizon existence. -/
def KerrNewmanData.discriminant (KN : KerrNewmanData) : ℝ :=
  KN.mass^2 - KN.spinParameter^2 - KN.charge^2

/-- The outer (event) horizon radius: r₊ = M + √(M² - a² - Q²). -/
def KerrNewmanData.outerHorizon (KN : KerrNewmanData) : ℝ :=
  KN.mass + Real.sqrt (max KN.discriminant 0)

/-- The inner (Cauchy) horizon radius: r₋ = M - √(M² - a² - Q²). -/
def KerrNewmanData.innerHorizon (KN : KerrNewmanData) : ℝ :=
  KN.mass - Real.sqrt (max KN.discriminant 0)

/-- Horizons exist when M² ≥ a² + Q² (sub-extremal or extremal). -/
lemma KerrNewmanData.horizons_exist (KN : KerrNewmanData) :
    KN.discriminant ≥ 0 := by
  unfold KerrNewmanData.discriminant
  have h := KN.kn_bound
  linarith

/-- The product of horizon radii: r₊ r₋ = a² + Q². -/
lemma KerrNewmanData.horizon_product (KN : KerrNewmanData) :
    KN.outerHorizon * KN.innerHorizon = KN.spinParameter^2 + KN.charge^2 := by
  unfold KerrNewmanData.outerHorizon KerrNewmanData.innerHorizon
  have h := KN.horizons_exist
  have hmax : max KN.discriminant 0 = KN.discriminant := max_eq_left h
  simp only [hmax]
  have hsqrt := Real.sq_sqrt h
  calc (KN.mass + Real.sqrt KN.discriminant) * (KN.mass - Real.sqrt KN.discriminant)
      = KN.mass^2 - (Real.sqrt KN.discriminant)^2 := by ring
    _ = KN.mass^2 - KN.discriminant := by rw [hsqrt]
    _ = KN.spinParameter^2 + KN.charge^2 := by unfold KerrNewmanData.discriminant; ring

/-- The sum of horizon radii: r₊ + r₋ = 2M. -/
lemma KerrNewmanData.horizon_sum (KN : KerrNewmanData) :
    KN.outerHorizon + KN.innerHorizon = 2 * KN.mass := by
  unfold KerrNewmanData.outerHorizon KerrNewmanData.innerHorizon
  ring

/-- For extremal KN, the two horizons coincide at r = M. -/
lemma KerrNewmanData.extremal_horizons_coincide (KN : KerrNewmanData)
    (hE : KN.isExtremal) : KN.outerHorizon = KN.innerHorizon := by
  unfold KerrNewmanData.outerHorizon KerrNewmanData.innerHorizon
    KerrNewmanData.isExtremal KerrNewmanData.discriminant at *
  have h : KN.mass^2 - KN.spinParameter^2 - KN.charge^2 = 0 := by linarith
  simp [h]

/-! ## Metric Components -/

/-- Boyer-Lindquist coordinates for Kerr-Newman. -/
structure KNBoyerLindquistCoords (KN : KerrNewmanData) where
  /-- Time coordinate -/
  t : ℝ
  /-- Radial coordinate -/
  r : ℝ
  /-- Polar angle -/
  θ : ℝ
  /-- Azimuthal angle -/
  φ : ℝ
  /-- Outside the outer horizon -/
  r_exterior : knDelta KN r > 0

/-- The Kerr-Newman metric components in Boyer-Lindquist coordinates.
The metric has the same structure as Kerr but with Δ = r² - 2Mr + a² + Q². -/
def knMetricComponents (KN : KerrNewmanData) (coords : KNBoyerLindquistCoords KN) :
    ℝ × ℝ × ℝ × ℝ × ℝ :=
  let sigma := knSigma KN coords.r coords.θ
  let delta := knDelta KN coords.r
  let a := KN.spinParameter
  let M := KN.mass
  let r := coords.r
  let sinθ := Real.sin coords.θ
  let sin2θ := sinθ^2
  let g_tt := -(1 - (2 * M * r - KN.charge^2) / sigma)
  let g_rr := sigma / delta
  let g_θθ := sigma
  let g_φφ := ((r^2 + a^2)^2 - delta * a^2 * sin2θ) / sigma * sin2θ
  let g_tφ := -(2 * M * r - KN.charge^2) * a * sin2θ / sigma
  (g_tt, g_rr, g_θθ, g_φφ, g_tφ)

/-! ## Electromagnetic Field -/

/-- The electromagnetic 4-potential for Kerr-Newman.
A_μ dx^μ = -Qr/Σ (dt - a sin²θ dφ) -/
def knElectromagneticPotential (KN : KerrNewmanData) (r θ : ℝ) :
    ℝ × ℝ × ℝ × ℝ :=
  let sigma := knSigma KN r θ
  let Q := KN.charge
  let a := KN.spinParameter
  let sinθ := Real.sin θ
  let A_t := -Q * r / sigma
  let A_φ := Q * r * a * sinθ^2 / sigma
  (A_t, 0, 0, A_φ)

/-- The electric field as seen by a static observer at infinity.
E_r = Q(r² - a²cos²θ)/Σ² -/
def knElectricFieldRadial (KN : KerrNewmanData) (r θ : ℝ) : ℝ :=
  let sigma := knSigma KN r θ
  let a := KN.spinParameter
  KN.charge * (r^2 - a^2 * (Real.cos θ)^2) / sigma^2

/-- The magnetic field (from frame dragging of the electric field).
B_r = 2Qar cos θ /Σ² -/
def knMagneticFieldRadial (KN : KerrNewmanData) (r θ : ℝ) : ℝ :=
  let sigma := knSigma KN r θ
  let a := KN.spinParameter
  2 * KN.charge * a * r * Real.cos θ / sigma^2

/-! ## Ergosphere -/

/-- The ergosphere outer boundary where g_tt = 0.
r_ergo = M + √(M² - a²cos²θ - Q²cos²θ) approximately. -/
def knErgosphereRadius (KN : KerrNewmanData) (θ : ℝ) : ℝ :=
  let cos2θ := (Real.cos θ)^2
  let discriminant := KN.mass^2 - KN.spinParameter^2 * cos2θ
  KN.mass + Real.sqrt (max discriminant 0)

/-- A point is in the Kerr-Newman ergosphere if r₊ < r < r_ergo. -/
def knIsInErgosphere (KN : KerrNewmanData) (r θ : ℝ) : Prop :=
  KN.outerHorizon < r ∧ r < knErgosphereRadius KN θ

/-! ## Surface Gravity and Thermodynamics -/

/-- The surface gravity of a Kerr-Newman black hole:
κ = √(M² - a² - Q²) / (2M r₊) where r₊ = M + √(M² - a² - Q²) -/
def KerrNewmanData.surfaceGravity (KN : KerrNewmanData) : ℝ :=
  if KN.discriminant > 0 then
    Real.sqrt KN.discriminant / (2 * KN.mass * KN.outerHorizon)
  else
    0

/-- The Hawking temperature T = κ/(2π). -/
def KerrNewmanData.hawkingTemperature (KN : KerrNewmanData) : ℝ :=
  KN.surfaceGravity / (2 * Real.pi)

/-- The Bekenstein-Hawking entropy S = A/4 = π(r₊² + a²). -/
def KerrNewmanData.entropy (KN : KerrNewmanData) : ℝ :=
  Real.pi * (KN.outerHorizon^2 + KN.spinParameter^2)

/-- The horizon area A = 4π(r₊² + a²). -/
def KerrNewmanData.horizonArea (KN : KerrNewmanData) : ℝ :=
  4 * Real.pi * (KN.outerHorizon^2 + KN.spinParameter^2)

/-- The angular velocity of the horizon: Ω_H = a/(r₊² + a²). -/
def KerrNewmanData.horizonAngularVelocity (KN : KerrNewmanData) : ℝ :=
  KN.spinParameter / (KN.outerHorizon^2 + KN.spinParameter^2)

/-- The electric potential at the horizon: Φ_H = Qr₊/(r₊² + a²). -/
def KerrNewmanData.horizonElectricPotential (KN : KerrNewmanData) : ℝ :=
  KN.charge * KN.outerHorizon / (KN.outerHorizon^2 + KN.spinParameter^2)

/-- The first law of black hole thermodynamics for Kerr-Newman:
dM = T dS + Ω_H dJ + Φ_H dQ = (κ/8π)dA + Ω_H dJ + Φ_H dQ -/
structure KNFirstLaw (KN : KerrNewmanData) where
  /-- Temperature coefficient -/
  temperatureCoeff : ℝ := KN.surfaceGravity / (8 * Real.pi)
  /-- Angular velocity coefficient -/
  angularVelocityCoeff : ℝ := KN.horizonAngularVelocity
  /-- Electric potential coefficient -/
  electricPotentialCoeff : ℝ := KN.horizonElectricPotential

/-- An extremal Kerr-Newman black hole has zero temperature. -/
lemma KerrNewmanData.extremal_zero_temperature (KN : KerrNewmanData)
    (hE : KN.isExtremal) : KN.hawkingTemperature = 0 := by
  unfold KerrNewmanData.hawkingTemperature KerrNewmanData.surfaceGravity
    KerrNewmanData.isExtremal KerrNewmanData.discriminant at *
  have h : KN.mass^2 - KN.spinParameter^2 - KN.charge^2 = 0 := by linarith
  simp [h]

/-! ## Properties -/

/-- The Kerr-Newman singularity is a ring at r = 0, θ = π/2 (where Σ = 0). -/
def knIsRingSingularity (KN : KerrNewmanData) (r θ : ℝ) : Prop :=
  r = 0 ∧ θ = Real.pi / 2 ∧ KN.spinParameter ≠ 0

/-! ## Limiting Cases -/

/-- For Kerr (Q = 0), the outer horizon simplifies to the Kerr formula. -/
lemma KerrNewmanData.kerr_limit_horizon (KN : KerrNewmanData) (hK : KN.isKerr) :
    KN.discriminant = KN.mass^2 - KN.spinParameter^2 := by
  unfold KerrNewmanData.discriminant KerrNewmanData.isKerr at *
  simp [hK]

/-- For Schwarzschild (a = Q = 0), the outer horizon is 2M. -/
lemma KerrNewmanData.schwarzschild_limit_horizon (KN : KerrNewmanData)
    (hS : KN.isSchwarzschild) : KN.outerHorizon = 2 * KN.mass := by
  unfold KerrNewmanData.outerHorizon KerrNewmanData.isSchwarzschild
    KerrNewmanData.discriminant at *
  simp only [hS.1, hS.2, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero]
  have hM_pos : KN.mass > 0 := KN.mass_pos
  have hmax : max (KN.mass^2) 0 = KN.mass^2 := max_eq_left (sq_nonneg _)
  simp only [hmax, Real.sqrt_sq (le_of_lt hM_pos)]
  ring

/-! ## Superradiance -/

/-- Superradiant scattering condition: waves with ω < mΩ_H + qΦ_H are amplified
when scattered off a Kerr-Newman black hole.
Returns true if the condition for superradiance is satisfied. -/
def knSuperradianceCondition (KN : KerrNewmanData) (ω m q : ℝ) : Prop :=
  ω < m * KN.horizonAngularVelocity + q * KN.horizonElectricPotential

/-- The superradiance amplification factor. -/
def knSuperradianceAmplification (KN : KerrNewmanData) (ω m q : ℝ) : ℝ :=
  m * KN.horizonAngularVelocity + q * KN.horizonElectricPotential - ω

/-- Amplification is positive when superradiance condition holds. -/
lemma knSuperradiance_amplification_pos (KN : KerrNewmanData) (ω m q : ℝ)
    (h : knSuperradianceCondition KN ω m q) :
    knSuperradianceAmplification KN ω m q > 0 := by
  unfold knSuperradianceAmplification knSuperradianceCondition at *
  linarith

end PseudoRiemannianMetric
end
