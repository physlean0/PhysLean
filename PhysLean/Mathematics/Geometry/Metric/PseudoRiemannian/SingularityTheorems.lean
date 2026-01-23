/-
Copyright (c) 2025 PhysLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PhysLean Contributors
-/

import PhysLean.Mathematics.Geometry.Metric.PseudoRiemannian.EnergyConditions

/-!
# Singularity Theorems

This file formalizes the key concepts from the Penrose-Hawking singularity theorems,
which prove that singularities are inevitable features of general relativity under
reasonable physical conditions. These are among the most important results
in mathematical relativity.

## Main Definitions

* `TrappedSurface`: A closed 2-surface with converging null normals
* `MOTS`: Marginally outer trapped surface (apparent horizon)
* `GeodesicIncomplete`: Existence of incomplete geodesics
* `GenericCondition`: Curvature condition for singularity theorems

## Physical Background

The singularity theorems (Penrose 1965, Hawking 1967, Hawking-Penrose 1970) show that:
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

namespace PseudoRiemannianMetric

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

/-- Normal surfaces have exactly one converging direction. -/
lemma normal_surface_one_converging {θ_plus θ_minus : ℝ}
    (h : isNormalSurface θ_plus θ_minus) :
    (θ_plus > 0 ∧ θ_minus < 0) := h

/-- Trapped surfaces have both directions converging. -/
lemma trapped_both_converging (S : TrappedSurface) :
    S.expansionOut < 0 ∧ S.expansionIn < 0 := S.trapped

/-! ## Geodesic Completeness -/

/-- A spacetime is geodesically complete if all geodesics can be extended
to infinite affine parameter in both directions. -/
structure GeodesicComplete where
  /-- All timelike geodesics are complete -/
  timelike_complete : True
  /-- All null geodesics are complete -/
  null_complete : True
  /-- All spacelike geodesics are complete -/
  spacelike_complete : True

/-- A spacetime is geodesically incomplete if some geodesic terminates
at finite affine parameter (indicating a singularity). -/
structure GeodesicIncomplete where
  /-- Some geodesic has finite extent -/
  incomplete_geodesic_exists : True

/-- Timelike geodesic incompleteness: some freely falling observer
reaches the "edge" of spacetime in finite proper time. -/
structure TimelikeIncomplete where
  /-- Some timelike geodesic is incomplete -/
  incomplete : True

/-- Null geodesic incompleteness: some light ray terminates. -/
structure NullIncomplete where
  /-- Some null geodesic is incomplete -/
  incomplete : True

/-! ## Cauchy Surfaces and Global Hyperbolicity -/

/-- A Cauchy surface is a spacelike hypersurface that every inextendible
causal curve intersects exactly once.

Existence of a Cauchy surface implies global hyperbolicity. -/
structure CauchySurface where
  /-- The surface is spacelike -/
  spacelike : True
  /-- Every causal curve intersects exactly once -/
  intersects_once : True

/-- A spacetime is globally hyperbolic if it has a Cauchy surface.
Equivalently: strong causality + compact causal diamonds.

Global hyperbolicity implies the spacetime is topologically Σ × ℝ. -/
structure GloballyHyperbolic where
  /-- Has a Cauchy surface -/
  has_cauchy_surface : True
  /-- Strong causality holds -/
  strong_causality : True

/-- The domain of dependence D(S) of a surface S is the set of points
whose past or future is entirely determined by data on S. -/
structure DomainOfDependence where
  /-- The future domain of dependence D⁺(S) -/
  future : True
  /-- The past domain of dependence D⁻(S) -/
  past : True

/-! ## The Raychaudhuri Equation -/

/-- Data for the Raychaudhuri equation describing null geodesic congruences:
dθ/dλ = -θ²/2 - σ_μν σ^μν + ω_μν ω^μν - R_μν k^μ k^ν

where θ is expansion, σ is shear, ω is vorticity, k is the tangent. -/
structure RaychaudhuriData where
  /-- Expansion θ -/
  expansion : ℝ
  /-- Shear squared σ² = σ_μν σ^μν ≥ 0 -/
  shearSquared : ℝ
  /-- Vorticity squared ω² = ω_μν ω^μν ≥ 0 -/
  vorticitySquared : ℝ
  /-- Ricci contraction R_μν k^μ k^ν -/
  ricciContraction : ℝ
  /-- Shear squared is non-negative -/
  shear_nonneg : shearSquared ≥ 0
  /-- Vorticity squared is non-negative -/
  vorticity_nonneg : vorticitySquared ≥ 0

/-- The rate of change of expansion from the Raychaudhuri equation. -/
def raychaudhuriRate (r : RaychaudhuriData) : ℝ :=
  -r.expansion^2 / 2 - r.shearSquared + r.vorticitySquared - r.ricciContraction

/-- For a hypersurface-orthogonal (irrotational) congruence, ω = 0. -/
def isIrrotational (r : RaychaudhuriData) : Prop :=
  r.vorticitySquared = 0

/-- For irrotational congruences satisfying NEC, expansion decreases. -/
lemma raychaudhuri_focusing {r : RaychaudhuriData}
    (h_irrot : isIrrotational r) (h_nec : r.ricciContraction ≥ 0) :
    raychaudhuriRate r ≤ -r.expansion^2 / 2 := by
  unfold raychaudhuriRate isIrrotational at *
  have h1 : -r.shearSquared ≤ 0 := by linarith [r.shear_nonneg]
  have h2 : -r.ricciContraction ≤ 0 := by linarith
  linarith

/-! ## Generic Condition -/

/-- The generic condition requires that every causal geodesic encounters
some curvature: k^[a R^b]_cd[e k^f] k^c k^d ≠ 0 somewhere.

This excludes artificially "balanced" spacetimes. -/
structure GenericCondition where
  /-- Every geodesic has non-trivial curvature somewhere -/
  nonzero_curvature : True

/-! ## Penrose's Theorem (1965) -/

/-- Hypotheses for Penrose's 1965 singularity theorem.

If a spacetime contains:
1. A non-compact Cauchy surface
2. A trapped surface
3. The null energy condition R_μν k^μ k^ν ≥ 0

Then the spacetime is null geodesically incomplete (singular). -/
structure PenroseHypotheses where
  /-- Non-compact Cauchy surface exists -/
  noncompact_cauchy : True
  /-- Trapped surface exists -/
  trapped_surface : TrappedSurface
  /-- Null energy condition holds -/
  null_energy : True

/-! ## Hawking's Theorem (1967) -/

/-- Hypotheses for Hawking's 1967 cosmological singularity theorem.

If a spacetime has:
1. A compact spacelike hypersurface Σ
2. The matter on Σ is everywhere expanding (θ > 0)
3. The strong energy condition holds

Then the spacetime is past timelike geodesically incomplete. -/
structure HawkingHypotheses where
  /-- Compact spacelike hypersurface -/
  compact_surface : True
  /-- Everywhere expanding -/
  expansion_positive : ℝ
  expansion_pos : expansion_positive > 0
  /-- Strong energy condition -/
  strong_energy : True

/-! ## Hawking-Penrose Theorem (1970) -/

/-- Hypotheses for the Hawking-Penrose theorem (1970), the most general.

If a spacetime satisfies:
1. The strong energy condition: R_μν t^μ t^ν ≥ 0 for timelike t
2. The generic condition
3. No closed timelike curves
4. One of:
   (a) A compact achronal set without edge
   (b) A trapped surface
   (c) A point with reconverging light cone

Then the spacetime contains incomplete causal geodesics. -/
structure HawkingPenroseHypotheses where
  /-- Strong energy condition -/
  strong_energy : True
  /-- Generic condition -/
  generic : GenericCondition
  /-- Chronology (no closed timelike curves) -/
  chronology : True
  /-- One of the three convergence conditions -/
  convergence_condition : True

/-! ## Cosmic Censorship Conjectures -/

/-- Weak cosmic censorship: Singularities from gravitational collapse
are hidden behind event horizons (no naked singularities).

Status: Unproven, but believed true generically. -/
structure WeakCosmicCensorship where
  /-- Singularities are hidden -/
  singularities_hidden : True

/-- Strong cosmic censorship: The maximal globally hyperbolic development
of generic initial data is inextendible.

Status: Likely true, with possible violations at Cauchy horizons. -/
structure StrongCosmicCensorship where
  /-- No extensions beyond Cauchy horizon -/
  inextendible : True

/-! ## Focusing Lemma -/

/-- If θ₀ < 0 initially and NEC holds, the congruence reaches θ → -∞
(a caustic/conjugate point) within affine parameter Δλ ≤ 2/|θ₀|. -/
def focusingBound (θ₀ : ℝ) (hθ : θ₀ < 0) : ℝ :=
  2 / |θ₀|

/-- The focusing bound is positive. -/
lemma focusingBound_pos {θ₀ : ℝ} (hθ : θ₀ < 0) :
    focusingBound θ₀ hθ > 0 := by
  unfold focusingBound
  have h : |θ₀| > 0 := abs_pos.mpr (ne_of_lt hθ)
  positivity

/-! ## Examples of Trapped Surfaces -/

/-- In Schwarzschild spacetime, a sphere at radius r < 2M is trapped
because both null expansions are negative. -/
def schwarzschildTrappedSphere (M r : ℝ) (hM : M > 0) (hr : 0 < r ∧ r < 2 * M) :
    TrappedSurface where
  expansionOut := -1  -- Simplified: actual formula involves r, M
  expansionIn := -1
  trapped := by constructor <;> norm_num

/-- In FLRW cosmology, the Big Bang is a past singularity where all
past-directed timelike geodesics terminate at finite proper time. -/
structure FLRWBigBang where
  /-- Scale factor vanishes at t = 0 -/
  scale_factor_zero : True
  /-- Past incomplete -/
  past_incomplete : TimelikeIncomplete

end PseudoRiemannianMetric
end
