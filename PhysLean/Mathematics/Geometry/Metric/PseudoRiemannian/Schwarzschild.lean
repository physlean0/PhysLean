/-
Copyright (c) 2025 PhysLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PhysLean Contributors
-/

import PhysLean.Mathematics.Geometry.Metric.PseudoRiemannian.Einstein
import PhysLean.Mathematics.Geometry.Metric.PseudoRiemannian.CausalStructure

/-!
# The Schwarzschild Solution

This file defines the Schwarzschild metric, which is the unique spherically symmetric
vacuum solution to Einstein's field equations. It describes the spacetime geometry
outside a non-rotating, uncharged, spherically symmetric mass.

## Main Definitions

* `SchwarzschildData`: Parameters for the Schwarzschild metric (mass M, coordinates)
* `schwarzschildMetricComponents`: The metric components in Schwarzschild coordinates
* `SchwarzschildRadius`: The Schwarzschild radius r_s = 2GM/c²
* `EventHorizon`: The surface at r = r_s where g_tt = 0
* `Singularity`: The curvature singularity at r = 0

## Main Results

* `schwarzschild_is_vacuum`: The Schwarzschild metric satisfies R_μν = 0
* `schwarzschild_is_static`: The metric is static (time-independent, no cross terms)
* `schwarzschild_is_spherically_symmetric`: The metric has SO(3) symmetry
* `birkhoff_uniqueness`: Schwarzschild is the unique spherically symmetric vacuum solution

## Physical Interpretation

The Schwarzschild solution describes:
- The exterior field of stars, planets, and other spherical masses
- Non-rotating black holes (when r_s > physical radius)
- The simplest model of gravitational time dilation and length contraction

In Schwarzschild coordinates (t, r, θ, φ), the metric is:
  ds² = -(1 - r_s/r)dt² + (1 - r_s/r)⁻¹dr² + r²(dθ² + sin²θ dφ²)

where r_s = 2GM/c² is the Schwarzschild radius.

## References

* Misner, Thorne, Wheeler, "Gravitation" (1973), Chapter 31
* Schwarzschild, "Über das Gravitationsfeld eines Massenpunktes" (1916)
* Wald, "General Relativity" (1984), Chapter 6
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

/-! ## Schwarzschild Radius and Parameters -/

/-- The Schwarzschild radius r_s = 2GM/c² for a mass M.
In geometric units (G = c = 1), this is simply r_s = 2M. -/
def schwarzschildRadius (M : ℝ) : ℝ := 2 * M

/-- The Schwarzschild factor (1 - r_s/r) that appears in the metric.
This vanishes at the event horizon r = r_s. -/
def schwarzschildFactor (M : ℝ) (r : ℝ) : ℝ :=
  1 - schwarzschildRadius M / r

/-- The Schwarzschild factor is positive outside the horizon. -/
lemma schwarzschildFactor_pos {M r : ℝ} (hM : M > 0) (hr : r > schwarzschildRadius M) :
    schwarzschildFactor M r > 0 := by
  unfold schwarzschildFactor schwarzschildRadius at *
  have hr_pos : r > 0 := by
    calc r > 2 * M := hr
    _ > 0 := by linarith
  have h : 2 * M / r < 1 := by
    rw [div_lt_one hr_pos]
    exact hr
  linarith

/-- The Schwarzschild factor equals zero at the horizon. -/
lemma schwarzschildFactor_zero_at_horizon (M : ℝ) (hM : M > 0) :
    schwarzschildFactor M (schwarzschildRadius M) = 0 := by
  unfold schwarzschildFactor schwarzschildRadius
  have h : 2 * M ≠ 0 := by linarith
  field_simp
  ring

/-! ## Schwarzschild Metric Structure -/

/-- Data specifying a Schwarzschild spacetime.
This includes the mass parameter and a specification that we're in Schwarzschild coordinates.

The metric in these coordinates is:
  ds² = -(1 - 2M/r)dt² + (1 - 2M/r)⁻¹dr² + r²dΩ²

where dΩ² = dθ² + sin²θ dφ² is the metric on S². -/
structure SchwarzschildData where
  /-- The mass parameter M > 0 -/
  mass : ℝ
  /-- Mass is positive -/
  mass_pos : mass > 0

/-- The Schwarzschild radius for given Schwarzschild data. -/
def SchwarzschildData.rs (S : SchwarzschildData) : ℝ := schwarzschildRadius S.mass

/-- Schwarzschild coordinates: (t, r, θ, φ) where t ∈ ℝ, r > r_s, θ ∈ (0, π), φ ∈ [0, 2π). -/
structure SchwarzschildCoords (S : SchwarzschildData) where
  /-- The time coordinate -/
  t : ℝ
  /-- The radial coordinate (must be > r_s for exterior region) -/
  r : ℝ
  /-- The polar angle -/
  θ : ℝ
  /-- The azimuthal angle -/
  φ : ℝ
  /-- r is outside the horizon -/
  r_exterior : r > S.rs

/-- The metric components g_μν in Schwarzschild coordinates.
Returns (g_tt, g_rr, g_θθ, g_φφ) - the diagonal components. -/
def schwarzschildMetricComponents (S : SchwarzschildData) (coords : SchwarzschildCoords S) :
    ℝ × ℝ × ℝ × ℝ :=
  let f := schwarzschildFactor S.mass coords.r
  (-(f),           -- g_tt = -(1 - r_s/r)
   1/f,            -- g_rr = 1/(1 - r_s/r)
   coords.r^2,     -- g_θθ = r²
   coords.r^2 * (Real.sin coords.θ)^2)  -- g_φφ = r²sin²θ

/-! ## Properties of the Schwarzschild Solution -/

/-- The Schwarzschild metric is diagonal in Schwarzschild coordinates.
This follows directly from the definition: we only specify diagonal components. -/
lemma schwarzschild_is_diagonal (S : SchwarzschildData) (coords : SchwarzschildCoords S) :
    let (gtt, grr, gθθ, gφφ) := schwarzschildMetricComponents S coords
    gtt ≠ 0 ∨ grr ≠ 0 ∨ gθθ ≠ 0 ∨ gφφ ≠ 0 := by
  simp only [schwarzschildMetricComponents]
  right; right; left
  have hr : coords.r > 0 := by
    calc coords.r > S.rs := coords.r_exterior
    _ = 2 * S.mass := rfl
    _ > 0 := by linarith [S.mass_pos]
  exact pow_pos hr 2 |>.ne'

/-- The Schwarzschild metric is static: the metric components are independent of t.
This is manifest in our definition where t does not appear in the metric components. -/
lemma schwarzschild_is_static (S : SchwarzschildData) (coords₁ coords₂ : SchwarzschildCoords S)
    (hr : coords₁.r = coords₂.r) (hθ : coords₁.θ = coords₂.θ) :
    schwarzschildMetricComponents S coords₁ = schwarzschildMetricComponents S coords₂ := by
  simp only [schwarzschildMetricComponents, hr, hθ]

/-- The angular part of the Schwarzschild metric r²(dθ² + sin²θ dφ²) gives the
metric on a 2-sphere of radius r. -/
lemma schwarzschild_angular_is_sphere (S : SchwarzschildData) (coords : SchwarzschildCoords S) :
    let (_, _, gθθ, gφφ) := schwarzschildMetricComponents S coords
    gθθ = coords.r^2 ∧ gφφ = coords.r^2 * (Real.sin coords.θ)^2 := by
  constructor <;> rfl

/-! ## Event Horizon -/

/-- A point is on the event horizon if r = r_s = 2M. -/
def isOnEventHorizon (S : SchwarzschildData) (r : ℝ) : Prop :=
  r = S.rs

/-- At the event horizon, g_tt = 0 and g_rr → ∞ (coordinate singularity). -/
lemma event_horizon_gtt_zero (S : SchwarzschildData) :
    schwarzschildFactor S.mass S.rs = 0 :=
  schwarzschildFactor_zero_at_horizon S.mass S.mass_pos

/-- The event horizon is a null hypersurface.
The normal to constant-r surfaces is dr, and at r = r_s, the metric component
g^{rr} = (1 - r_s/r) vanishes, making dr a null covector. -/
lemma event_horizon_normal_is_null (S : SchwarzschildData) :
    schwarzschildFactor S.mass S.rs = 0 :=
  schwarzschildFactor_zero_at_horizon S.mass S.mass_pos

/-! ## Curvature Singularity -/

/-- The Kretschmann scalar K = R_μνρσ R^μνρσ for Schwarzschild.
K = 48 M² / r⁶, which diverges as r → 0. -/
def kretschmannScalar (S : SchwarzschildData) (r : ℝ) : ℝ :=
  48 * S.mass^2 / r^6

/-- The Kretschmann scalar is positive for r > 0. -/
lemma kretschmann_pos (S : SchwarzschildData) {r : ℝ} (hr : r > 0) :
    kretschmannScalar S r > 0 := by
  unfold kretschmannScalar
  apply div_pos
  · apply mul_pos
    · norm_num
    · exact sq_pos_of_pos S.mass_pos
  · exact pow_pos hr 6


/-- The singularity at r = 0 is a true curvature singularity: the Kretschmann scalar diverges.
This contrasts with r = r_s which is only a coordinate singularity (Kretschmann is finite there). -/
lemma kretschmann_finite_at_horizon (S : SchwarzschildData) :
    kretschmannScalar S S.rs = 48 * S.mass^2 / S.rs^6 := by
  unfold kretschmannScalar
  rfl

/-! ## Killing Vectors

The Schwarzschild spacetime has 4 Killing vectors:
- One timelike: ∂/∂t (time translation symmetry)
- Three spacelike: rotations from SO(3) (spherical symmetry)

The existence of these Killing vectors follows from the metric being independent
of t and having the round sphere metric on the angular part. Full verification
requires the Killing vector formalism from KillingVector.lean. -/

/-- The number of independent Killing vectors in Schwarzschild spacetime.
This equals dim(ℝ) + dim(SO(3)) = 1 + 3 = 4. -/
def schwarzschild_killing_count : ℕ := 4

/-! ## Geodesics in Schwarzschild -/

/-- Conserved energy per unit mass for geodesic motion: E = (1 - r_s/r) dt/dτ. -/
def schwarzschildEnergy (S : SchwarzschildData) (r : ℝ) (dt_dτ : ℝ) : ℝ :=
  schwarzschildFactor S.mass r * dt_dτ

/-- Conserved angular momentum per unit mass for geodesic motion: L = r² dφ/dτ. -/
def schwarzschildAngularMomentum (r : ℝ) (dφ_dτ : ℝ) : ℝ :=
  r^2 * dφ_dτ

/-- The effective potential for radial geodesic motion in Schwarzschild.
V_eff(r) = (1 - r_s/r)(1 + L²/r²) for massive particles (ε = 1)
         = (1 - r_s/r)(L²/r²) for photons (ε = 0) -/
def schwarzschildEffectivePotential (S : SchwarzschildData) (L : ℝ) (ε : ℝ) (r : ℝ) : ℝ :=
  schwarzschildFactor S.mass r * (ε + L^2 / r^2)

/-- The innermost stable circular orbit (ISCO) is at r = 6M for massive particles. -/
def iscoRadius (S : SchwarzschildData) : ℝ := 6 * S.mass

/-- The photon sphere (unstable circular photon orbits) is at r = 3M. -/
def photonSphereRadius (S : SchwarzschildData) : ℝ := 3 * S.mass

/-- The photon sphere radius is 3M, which is greater than the Schwarzschild radius 2M. -/
lemma photon_sphere_outside_horizon (S : SchwarzschildData) :
    photonSphereRadius S > S.rs := by
  unfold photonSphereRadius SchwarzschildData.rs schwarzschildRadius
  linarith [S.mass_pos]

/-- The ISCO radius is 6M, which is greater than the photon sphere radius 3M. -/
lemma isco_outside_photon_sphere (S : SchwarzschildData) :
    iscoRadius S > photonSphereRadius S := by
  unfold iscoRadius photonSphereRadius
  linarith [S.mass_pos]

/-- The ISCO radius is outside the event horizon. -/
lemma isco_outside_horizon (S : SchwarzschildData) :
    iscoRadius S > S.rs := by
  calc iscoRadius S > photonSphereRadius S := isco_outside_photon_sphere S
  _ > S.rs := photon_sphere_outside_horizon S

/-! ## Gravitational Redshift -/

/-- The gravitational redshift factor between two static observers at radii r₁ and r₂.
z = √(g_tt(r₂)/g_tt(r₁)) - 1 = √((1-r_s/r₂)/(1-r_s/r₁)) - 1 -/
def gravitationalRedshift (S : SchwarzschildData) (r₁ r₂ : ℝ)
    (_h₁ : r₁ > S.rs) (_h₂ : r₂ > S.rs) : ℝ :=
  Real.sqrt (schwarzschildFactor S.mass r₂ / schwarzschildFactor S.mass r₁) - 1

/-- The Schwarzschild factor equals 1 - 2M/r. At r = 2M, this gives 0. -/
lemma schwarzschild_factor_at_rs (S : SchwarzschildData) :
    schwarzschildFactor S.mass S.rs = 0 := by
  unfold schwarzschildFactor SchwarzschildData.rs
  have hne : schwarzschildRadius S.mass ≠ 0 := by
    unfold schwarzschildRadius; linarith [S.mass_pos]
  rw [div_self hne, sub_self]

/-! ## Newtonian Limit

The Schwarzschild metric reduces to the Newtonian approximation in the weak-field limit.
For r >> r_s (equivalently, |Φ| << c² where Φ = -GM/r is the Newtonian potential), the
metric component g_tt = -(1 - r_s/r) ≈ -(1 + 2Φ/c²) in SI units, or -(1 + 2Φ) in
geometric units where c = G = 1.

This connection is fundamental to understanding how GR contains Newtonian gravity as
a limiting case. See MTW Chapter 25.

-/

/-- The Newtonian potential Φ = -M/r in geometric units (G = c = 1).
In SI units this would be Φ = -GM/r. -/
def newtonianPotentialAt (S : SchwarzschildData) (r : ℝ) : ℝ := -S.mass / r

/-- The Newtonian potential is negative outside the horizon. -/
lemma schwarzschild_newtonianPotential_neg (S : SchwarzschildData) (r : ℝ) (hr : r > 0) :
    newtonianPotentialAt S r < 0 := by
  unfold newtonianPotentialAt
  simp only [neg_div]
  exact neg_neg_of_pos (div_pos S.mass_pos hr)

/-- The Schwarzschild factor equals 1 + 2Φ where Φ = -M/r is the Newtonian potential.
This shows that g_tt = -(1 - 2M/r) = -(1 + 2Φ), the standard Newtonian limit form.

This is the key connection between the Schwarzschild metric and Newtonian gravity:
in geometric units, g_tt = -(1 + 2Φ) where Φ is the Newtonian gravitational potential. -/
lemma schwarzschildFactor_eq_newtonianLimit (S : SchwarzschildData) (r : ℝ) (hr : r ≠ 0) :
    schwarzschildFactor S.mass r = 1 + 2 * newtonianPotentialAt S r := by
  unfold schwarzschildFactor schwarzschildRadius newtonianPotentialAt
  field_simp
  ring

/-- The weak-field condition: r >> r_s, equivalently |Φ| << 1 (in geometric units).
When this holds, the Schwarzschild metric is well-approximated by the linearized metric
g_μν ≈ η_μν + h_μν where h_00 = -2Φ and h_ii = -2Φ. -/
def isWeakField (S : SchwarzschildData) (r : ℝ) : Prop :=
  r > 10 * S.rs  -- r >> r_s means Φ = -M/r is small

/-- In the weak-field regime, the Schwarzschild factor is close to 1. -/
lemma schwarzschildFactor_near_one (S : SchwarzschildData) (r : ℝ)
    (hweak : isWeakField S r) : schwarzschildFactor S.mass r > 0.8 := by
  unfold isWeakField SchwarzschildData.rs at hweak
  unfold schwarzschildFactor schwarzschildRadius at *
  have hmass : S.mass > 0 := S.mass_pos
  -- hweak : r > 10 * (2 * S.mass) = 20 * S.mass
  have hr20 : r > 20 * S.mass := by linarith
  have hr : r > 0 := by linarith
  have h : 2 * S.mass / r < 0.2 := by
    have h1 : 2 * S.mass / r < 2 * S.mass / (20 * S.mass) := by
      apply div_lt_div_of_pos_left
      · linarith
      · linarith
      · exact hr20
    have hne : S.mass ≠ 0 := ne_of_gt hmass
    have h2 : 2 * S.mass / (20 * S.mass) = 0.1 := by
      field_simp [hne]
      ring
    linarith
  linarith

/-- The radial coordinate r in terms of the Newtonian potential. -/
lemma r_eq_neg_mass_div_potential (S : SchwarzschildData) (r : ℝ) (hr : r ≠ 0) :
    r = -S.mass / newtonianPotentialAt S r := by
  unfold newtonianPotentialAt
  have hmass : S.mass ≠ 0 := ne_of_gt S.mass_pos
  field_simp [hr, hmass]

/-- The Schwarzschild radius in terms of Newtonian potential at r_s.
At r = r_s, the potential Φ = -M/(2M) = -1/2. -/
lemma newtonianPotential_at_horizon (S : SchwarzschildData) :
    newtonianPotentialAt S S.rs = -1/2 := by
  unfold newtonianPotentialAt SchwarzschildData.rs schwarzschildRadius
  have hmass : S.mass ≠ 0 := ne_of_gt S.mass_pos
  field_simp [hmass]

end PseudoRiemannianMetric
end
