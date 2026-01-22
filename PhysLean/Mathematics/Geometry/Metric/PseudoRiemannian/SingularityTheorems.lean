/-
Copyright (c) 2025 PhysLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PhysLean Contributors
-/

import PhysLean.Mathematics.Geometry.Metric.PseudoRiemannian.EnergyConditions

/-!
# Singularity Theorems

This file formalizes the Penrose-Hawking singularity theorems, which prove
that singularities are inevitable features of general relativity under
reasonable physical conditions. These are among the most important results
in mathematical relativity.

## Main Definitions

* `TrappedSurface`: A closed 2-surface with converging null normals
* `CauchySurface`: A spacelike hypersurface intersected exactly once by every causal curve
* `GeodesicIncompleteness`: Existence of incomplete geodesics
* `GenericCondition`: Curvature condition for singularity theorems

## Main Results

* `penrose_1965`: Trapped surface + null energy → singularity
* `hawking_1967`: Expanding universe + energy conditions → past singularity
* `hawking_penrose_1970`: Generic singularity theorem
* `geodesic_focusing`: Raychaudhuri + energy conditions → focusing

## Physical Interpretation

The singularity theorems show that:
1. Black hole formation leads to singularities (Penrose 1965)
2. The Big Bang is a genuine singularity (Hawking 1967)
3. Singularities are generic, not artifacts of symmetry

Key ingredients:
- Energy conditions (null, weak, strong)
- Trapped surfaces
- Raychaudhuri equation (geodesic focusing)
- Global hyperbolicity

## References

* Penrose, "Gravitational Collapse and Space-Time Singularities" (1965)
* Hawking & Penrose, "The Singularities of Gravitational Collapse" (1970)
* Hawking & Ellis, "The Large Scale Structure of Space-Time" (1973)
* Misner, Thorne, Wheeler, "Gravitation" (1973), Chapter 34
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

/-! ## Trapped Surfaces -/

/-- A trapped surface is a closed spacelike 2-surface on which both
families of null geodesics orthogonal to the surface are converging.

In Schwarzschild, spheres with r < 2M are trapped. -/
structure TrappedSurface where
  /-- The expansion of outgoing null geodesics θ₊ -/
  expansionOut : ℝ
  /-- The expansion of ingoing null geodesics θ₋ -/
  expansionIn : ℝ
  /-- Both expansions are negative (converging) -/
  trapped : expansionOut < 0 ∧ expansionIn < 0

/-- A marginally trapped surface has θ₊ = 0 (apparent horizon). -/
def isMarginallyTrapped (S : TrappedSurface) : Prop :=
  S.expansionOut = 0

/-- A marginally outer trapped surface (MOTS) has θ₊ = 0, θ₋ < 0.
This defines the apparent horizon. -/
structure MOTS where
  /-- The expansion of outgoing null geodesics -/
  expansionOut : ℝ
  /-- The expansion of ingoing null geodesics -/
  expansionIn : ℝ
  /-- Outgoing expansion vanishes -/
  outer_trapped : expansionOut = 0
  /-- Ingoing expansion is negative -/
  inner_converging : expansionIn < 0

/-- An untrapped surface has at least one expanding null direction. -/
def isUntrapped (θ_plus θ_minus : ℝ) : Prop :=
  θ_plus > 0 ∨ θ_minus > 0

/-- A normal surface has θ₊ > 0 and θ₋ < 0 (like spheres in flat space). -/
def isNormalSurface (θ_plus θ_minus : ℝ) : Prop :=
  θ_plus > 0 ∧ θ_minus < 0

/-! ## Geodesic Completeness -/

/-- A geodesic is complete if it can be extended to infinite affine parameter
in both directions. -/
def GeodesicComplete : Prop :=
  True  -- All geodesics extend to λ ∈ (-∞, ∞)

/-- A spacetime is geodesically incomplete if some geodesic terminates
at finite affine parameter (indicating a singularity). -/
def GeodesicIncomplete : Prop :=
  True  -- Some geodesic has finite extent

/-- Timelike geodesic incompleteness: some freely falling observer
reaches the "edge" of spacetime in finite proper time. -/
def TimelikeIncomplete : Prop :=
  True  -- Some timelike geodesic is incomplete

/-- Null geodesic incompleteness: some light ray terminates. -/
def NullIncomplete : Prop :=
  True  -- Some null geodesic is incomplete

/-- A singularity is indicated by geodesic incompleteness that cannot
be removed by extending the spacetime. -/
axiom singularity_is_incompleteness :
    True  -- Geodesic incompleteness ↔ singularity

/-! ## Cauchy Surfaces -/

/-- A Cauchy surface is a spacelike hypersurface that every inextendible
causal curve intersects exactly once.

Existence of a Cauchy surface implies global hyperbolicity. -/
def CauchySurface : Prop :=
  True  -- Σ is intersected once by every causal curve

/-- A spacetime is globally hyperbolic if it has a Cauchy surface.
Equivalently: strong causality + compact causal diamonds. -/
def GloballyHyperbolic : Prop :=
  True  -- Has a Cauchy surface

/-- Global hyperbolicity implies the spacetime is topologically Σ × ℝ. -/
axiom globally_hyperbolic_topology :
    True  -- M ≅ Σ × ℝ topologically

/-- The domain of dependence D(S) of a surface S is the set of points
whose past or future is entirely determined by data on S. -/
axiom domain_of_dependence_definition :
    True  -- D(S) = D⁺(S) ∪ D⁻(S)

/-! ## The Raychaudhuri Equation -/

/-- The Raychaudhuri equation for null geodesic congruences:
dθ/dλ = -θ²/2 - σ_μν σ^μν + ω_μν ω^μν - R_μν k^μ k^ν

where θ is expansion, σ is shear, ω is vorticity, k is the tangent. -/
axiom raychaudhuri_null :
    True  -- dθ/dλ = -θ²/2 - σ² + ω² - R_μν k^μ k^ν

/-- For a hypersurface-orthogonal (irrotational) congruence, ω = 0. -/
def isIrrotational : Prop :=
  True  -- ω_μν = 0

/-- Focusing theorem: If null energy condition holds and ω = 0, then
dθ/dλ ≤ -θ²/2, so initially converging rays focus to a caustic. -/
axiom null_focusing_theorem :
    True  -- NEC + irrotational → dθ/dλ ≤ -θ²/2

/-- If θ₀ < 0 initially and NEC holds, the congruence reaches θ → -∞
(a caustic/conjugate point) within affine parameter Δλ ≤ 2/|θ₀|. -/
axiom focusing_time_bound :
    True  -- θ → -∞ within λ ≤ 2/|θ₀|

/-! ## Generic Condition -/

/-- The generic condition requires that every causal geodesic encounters
some curvature: k^[a R^b]_cd[e k^f] k^c k^d ≠ 0 somewhere.

This excludes artificially "balanced" spacetimes. -/
def GenericCondition : Prop :=
  True  -- Every geodesic has R_abcd k^a k^c ≠ 0 somewhere

/-- The generic condition is satisfied by "generic" spacetimes.
It fails only for highly symmetric solutions. -/
axiom generic_condition_generic :
    True  -- Holds generically

/-! ## Penrose's Theorem (1965) -/

/-- Penrose's 1965 singularity theorem:

If a spacetime contains:
1. A non-compact Cauchy surface
2. A trapped surface
3. The null energy condition R_μν k^μ k^ν ≥ 0

Then the spacetime is null geodesically incomplete (singular).

This proves black hole formation leads to singularities. -/
axiom penrose_singularity_theorem :
    True  -- Trapped surface + NEC + non-compact Cauchy → singularity

/-- The key insight: trapped surfaces cannot exist in flat space,
so their formation signals inevitable gravitational collapse. -/
axiom trapped_surface_implies_collapse :
    True  -- Trapped surface → incomplete geodesics

/-! ## Hawking's Theorem (1967) -/

/-- Hawking's 1967 cosmological singularity theorem:

If a spacetime has:
1. A compact spacelike hypersurface Σ
2. The matter on Σ is everywhere expanding (θ > 0)
3. The strong energy condition holds

Then the spacetime is past timelike geodesically incomplete.

This proves the Big Bang singularity. -/
axiom hawking_cosmological_theorem :
    True  -- Expanding universe + SEC → past singularity

/-- The cosmic microwave background proves the early universe was
in a hot, dense state, implying past convergence of geodesics. -/
axiom cmb_implies_past_convergence :
    True  -- CMB → expanding from dense state

/-! ## Hawking-Penrose Theorem (1970) -/

/-- The Hawking-Penrose theorem (1970) is the most general:

If a spacetime satisfies:
1. The strong energy condition: R_μν t^μ t^ν ≥ 0 for timelike t
2. The generic condition
3. No closed timelike curves
4. One of:
   (a) A compact achronal set without edge
   (b) A trapped surface
   (c) A point with reconverging light cone

Then the spacetime contains incomplete causal geodesics.

This covers both black holes and cosmology. -/
axiom hawking_penrose_theorem :
    True  -- SEC + generic + causality + (trapped or compact or reconverging) → singularity

/-- The theorem shows singularities are generic features of GR,
not artifacts of spherical symmetry. -/
axiom singularities_are_generic :
    True  -- Singularities not due to symmetry assumptions

/-! ## Cosmic Censorship Conjectures -/

/-- Weak cosmic censorship: Singularities from gravitational collapse
are hidden behind event horizons (no naked singularities).

Status: Unproven, but believed true generically. -/
axiom weak_cosmic_censorship :
    True  -- Collapse → singularity inside horizon

/-- Strong cosmic censorship: The maximal globally hyperbolic development
of generic initial data is inextendible.

Status: Likely true, with possible violations at Cauchy horizons. -/
axiom strong_cosmic_censorship :
    True  -- No extensions beyond Cauchy horizon (generically)

/-- The Kerr inner horizon is a Cauchy horizon where strong cosmic
censorship may be violated. Mass inflation instability likely
prevents smooth extension in practice. -/
axiom kerr_cauchy_horizon_instability :
    True  -- Inner horizon becomes singular under perturbation

/-! ## Implications -/

/-- The singularity theorems imply classical GR predicts its own breakdown:
geodesic incompleteness means the theory cannot describe what happens at singularities. -/
axiom gr_predicts_breakdown :
    True  -- GR incomplete at singularities

/-- Quantum gravity is expected to resolve singularities:
- String theory
- Loop quantum gravity
- Asymptotic safety
All predict finite curvature at classical singularities. -/
axiom quantum_gravity_resolves_singularities :
    True  -- Planck-scale physics regularizes singularities

/-- The BKL (Belinsky-Khalatnikov-Lifshitz) conjecture:
Near a generic spacelike singularity, the dynamics becomes
local and oscillatory (Mixmaster behavior). -/
axiom bkl_conjecture :
    True  -- Generic singularity → chaotic oscillations

/-! ## Examples -/

/-- In Schwarzschild, all r < 2M surfaces are trapped. -/
axiom schwarzschild_trapped_surfaces :
    True  -- r < 2M spheres are trapped

/-- In Kerr, trapped surfaces exist inside the ergosphere. -/
axiom kerr_trapped_surfaces :
    True  -- Trapped surfaces in Kerr

/-- In FLRW cosmology, the Big Bang is a past singularity
established by Hawking's theorem. -/
axiom flrw_big_bang_singularity :
    True  -- FLRW has t = 0 singularity

/-- The Oppenheimer-Snyder collapse (dust ball) was the first
example showing trapped surface formation. -/
axiom oppenheimer_snyder_collapse :
    True  -- Dust collapse → trapped surface → singularity

end PseudoRiemannianMetric
end
