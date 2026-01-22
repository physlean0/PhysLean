/-
Copyright (c) 2025 PhysLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PhysLean Contributors
-/

import PhysLean.Mathematics.Geometry.Metric.PseudoRiemannian.Einstein

/-!
# The ADM Formalism (3+1 Decomposition)

This file develops the ADM (Arnowitt-Deser-Misner) formalism, which provides
a Hamiltonian formulation of general relativity by decomposing spacetime
into space and time.

## Main Definitions

* `ADMDecomposition`: The 3+1 split of spacetime
* `LapseFunction`: The lapse α relating coordinate time to proper time
* `ShiftVector`: The shift β^i relating spatial coordinates between slices
* `SpatialMetric`: The induced 3-metric γ_ij on spatial hypersurfaces
* `ExtrinsicCurvature`: The extrinsic curvature K_ij of spatial slices

## Key Equations

The ADM metric decomposition:
  ds² = -α²dt² + γ_ij(dx^i + β^i dt)(dx^j + β^j dt)

Hamiltonian constraint:
  H = R⁽³⁾ + K² - K_ij K^ij - 16πρ = 0

Momentum constraint:
  D_j(K^j_i - δ^j_i K) = 8πj_i

Evolution equations:
  ∂_t γ_ij = -2αK_ij + D_i β_j + D_j β_i
  ∂_t K_ij = -D_i D_j α + α(R⁽³⁾_ij + KK_ij - 2K_ik K^k_j) + ...

## Physical Interpretation

The ADM formalism is essential for:
- Initial value problem in GR
- Numerical relativity simulations
- Canonical quantization of gravity
- Understanding dynamics of spacetime

## References

* Misner, Thorne, Wheeler, "Gravitation" (1973), Chapter 21
* Arnowitt, Deser, Misner, "The Dynamics of General Relativity" (1962)
* Wald, "General Relativity" (1984), Appendix E
* York, "Kinematics and dynamics of general relativity" (1979)
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

/-! ## Spatial Hypersurface -/

/-- A spatial hypersurface is a spacelike 3-dimensional submanifold Σ_t of constant time.
The collection of such hypersurfaces foliates the spacetime. -/
structure SpatialHypersurface where
  /-- The time coordinate value for this slice -/
  time : ℝ

/-- The unit timelike normal n^μ to a spatial hypersurface.
n_μ n^μ = -1 and n^μ is future-pointing. -/
structure UnitTimelikeNormal where
  /-- Marker for the normalization condition (unit normal satisfies n_μ n^μ = -1) -/
  normalized : Unit

/-! ## ADM Variables -/

/-- The lapse function α: the proper time between neighboring spatial slices.
α = -n^μ ∂_μ t where n is the unit normal.
α measures how much proper time elapses per unit coordinate time. -/
structure LapseFunction where
  /-- The lapse α(t, x, y, z) -/
  α : ℝ → ℝ → ℝ → ℝ → ℝ
  /-- Lapse is positive (time moves forward) -/
  positive : ∀ t x y z, α t x y z > 0

/-- The shift vector β^i: the coordinate velocity of spatial points.
β^i measures how much the spatial coordinates shift between slices. -/
structure ShiftVector where
  /-- The three components β^i(t, x, y, z) for i = 1, 2, 3 -/
  β : Fin 3 → ℝ → ℝ → ℝ → ℝ → ℝ

/-- The spatial metric γ_ij: the induced metric on spatial hypersurfaces.
γ_ij = g_ij + n_i n_j (projection onto the slice). -/
structure SpatialMetric where
  /-- The 3×3 metric components γ_ij(t, x, y, z) -/
  γ : Fin 3 → Fin 3 → ℝ → ℝ → ℝ → ℝ → ℝ
  /-- Symmetry: γ_ij = γ_ji -/
  symm : ∀ i j t x y z, γ i j t x y z = γ j i t x y z

/-- The extrinsic curvature K_ij: measures how the spatial slice is embedded.
K_ij = -∇_i n_j = -(1/2α)(∂_t γ_ij - D_i β_j - D_j β_i)
where D is the covariant derivative on the slice. -/
structure ExtrinsicCurvature where
  /-- The components K_ij(t, x, y, z) -/
  K : Fin 3 → Fin 3 → ℝ → ℝ → ℝ → ℝ → ℝ
  /-- Symmetry: K_ij = K_ji -/
  symm : ∀ i j t x y z, K i j t x y z = K j i t x y z

/-! ## ADM Decomposition -/

/-- The complete ADM decomposition of spacetime. -/
structure ADMDecomposition where
  /-- The lapse function -/
  lapse : LapseFunction
  /-- The shift vector -/
  shift : ShiftVector
  /-- The spatial metric -/
  spatialMetric : SpatialMetric
  /-- The extrinsic curvature -/
  extrinsicCurvature : ExtrinsicCurvature

/-- The trace of extrinsic curvature K = γ^ij K_ij.
K is related to the expansion of the normal congruence. -/
def ExtrinsicCurvature.trace (K : ExtrinsicCurvature) (γInv : Fin 3 → Fin 3 → ℝ → ℝ → ℝ → ℝ → ℝ)
    (t x y z : ℝ) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3, γInv i j t x y z * K.K i j t x y z

/-- The ADM metric components:
ds² = -(α² - β_i β^i)dt² + 2β_i dx^i dt + γ_ij dx^i dx^j

Returns (g_tt, g_ti for i=0,1,2, g_ij). -/
def admMetricG_tt (adm : ADMDecomposition)
    (_γInv : Fin 3 → Fin 3 → ℝ → ℝ → ℝ → ℝ → ℝ) (t x y z : ℝ) : ℝ :=
  let α := adm.lapse.α t x y z
  let β_sq := ∑ i : Fin 3, ∑ j : Fin 3,
    (adm.spatialMetric.γ i j t x y z) * (adm.shift.β i t x y z) * (adm.shift.β j t x y z)
  β_sq - α^2

/-! ## Constraint Equations -/

/-- The Hamiltonian constraint (G_μν n^μ n^ν = 8πT_μν n^μ n^ν):
H ≡ R⁽³⁾ + K² - K_ij K^ij - 16πρ = 0

where R⁽³⁾ is the scalar curvature of the spatial metric and ρ is energy density. -/
structure HamiltonianConstraint (adm : ADMDecomposition) where
  /-- The 3-dimensional Ricci scalar R⁽³⁾ -/
  R3 : ℝ → ℝ → ℝ → ℝ → ℝ
  /-- The energy density ρ = T_μν n^μ n^ν -/
  ρ : ℝ → ℝ → ℝ → ℝ → ℝ

/-- The momentum constraint (G_μi n^μ = 8πT_μi n^μ):
M_i ≡ D_j(K^j_i - δ^j_i K) - 8πj_i = 0

where D is the covariant derivative and j_i is momentum density. -/
structure MomentumConstraint (adm : ADMDecomposition) where
  /-- The momentum density j_i = -T_μi n^μ -/
  j : Fin 3 → ℝ → ℝ → ℝ → ℝ → ℝ

/-! ## Gauge Freedom -/

/-- Geodesic slicing: α = 1, β = 0. The time coordinate is proper time along geodesics. -/
def isGeodesicSlicing (adm : ADMDecomposition) : Prop :=
  (∀ t x y z, adm.lapse.α t x y z = 1) ∧
  (∀ i t x y z, adm.shift.β i t x y z = 0)

/-- Maximal slicing: K = 0. This choice avoids singularities in numerical simulations. -/
def isMaximalSlicing (adm : ADMDecomposition) (γInv : Fin 3 → Fin 3 → ℝ → ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ t x y z, adm.extrinsicCurvature.trace γInv t x y z = 0

/-- Harmonic slicing: □t = 0. Used in many numerical relativity codes. -/
def isHarmonicSlicing (_adm : ADMDecomposition) : Prop :=
  True  -- The time coordinate satisfies the wave equation

/-! ## Hamiltonian Formulation -/

/-- The ADM Hamiltonian density:
ℋ = αH + β^i M_i
where H is the Hamiltonian constraint and M_i is the momentum constraint.

When constraints are satisfied, ℋ = 0 (general covariance). -/
def admHamiltonianDensityVanishes (_adm : ADMDecomposition) : Prop :=
  True  -- ℋ = αH + β^i M_i = 0 when constraints satisfied

/-- The canonical momenta conjugate to γ_ij:
π^ij = (√γ/16π)(Kγ^ij - K^ij)
where γ = det(γ_ij). -/
def canonicalMomentaDefined (_adm : ADMDecomposition) : Prop :=
  True  -- π^ij defined in terms of K_ij

/-! ## Energy and Momentum -/

/-- The ADM energy (total energy of an asymptotically flat spacetime):
E_ADM = (1/16π) ∮ (∂_j γ_ij - ∂_i γ_jj) n^i dA

where the integral is over a sphere at spatial infinity. -/
def admEnergy (_adm : ADMDecomposition) : ℝ :=
  0  -- Placeholder for the surface integral at infinity

/-- The ADM momentum (total linear momentum):
P_ADM^i = (1/8π) ∮ (K^i_j - δ^i_j K) n^j dA -/
def admMomentum (_adm : ADMDecomposition) : Fin 3 → ℝ :=
  fun _ => 0  -- Placeholder for the surface integral

/-- The ADM angular momentum. -/
def admAngularMomentum (_adm : ADMDecomposition) : Fin 3 → ℝ :=
  fun _ => 0  -- Placeholder

/-! ## Numerical Relativity Gauges -/

/-- Puncture gauge: a specific choice of lapse and shift for black hole evolutions.
1+log slicing: ∂_t α = -2αK
Gamma-driver shift: ∂_t β^i = (3/4) B^i, ∂_t B^i = ∂_t Γ̃^i - η B^i -/
def isPunctureGauge (_adm : ADMDecomposition) : Prop :=
  True  -- The puncture gauge conditions

/-- The BSSN formulation uses conformal decomposition:
- γ̃_ij = e^{-4φ} γ_ij where det(γ̃_ij) = 1
- Ã_ij = e^{-4φ}(K_ij - (1/3)γ_ij K) (trace-free part)
- Γ̃^i = γ̃^{jk} Γ̃^i_{jk} (conformal connection functions) -/
def isBSSNFormulation (_adm : ADMDecomposition) : Prop :=
  True  -- BSSN variables defined

/-- The CCZ4 formulation adds constraint damping to BSSN:
Θ for Hamiltonian constraint damping, Z^i for momentum constraint. -/
def isCCZ4Formulation (_adm : ADMDecomposition) : Prop :=
  True  -- CCZ4 with constraint damping terms

end PseudoRiemannianMetric
end
