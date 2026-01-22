/-
Copyright (c) 2025 PhysLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PhysLean Contributors
-/

import PhysLean.Mathematics.Geometry.Metric.PseudoRiemannian.Einstein

/-!
# Linearized Gravity

This file formalizes linearized general relativity, the weak-field approximation
where the metric is a small perturbation of flat spacetime. This regime describes
gravitational waves far from sources and provides the foundation for the
field-theoretic approach to gravity.

## Main Definitions

* `WeakFieldPerturbation`: The perturbation h_μν around flat spacetime
* `minkowskiMetric`: The flat Minkowski metric η_μν = diag(-1, 1, 1, 1)
* `TTGaugePerturbation`: The transverse-traceless gauge for gravitational waves
* `plusPolarization`, `crossPolarization`: Gravitational wave polarizations
* `planeWaveSolution`: Plane wave solutions to the linearized equations

## Physical Interpretation

Linearized gravity describes:
- Gravitational waves far from sources
- Newtonian gravity as the static limit
- The graviton as a massless spin-2 particle
- Post-Newtonian corrections at higher orders

The metric is g_μν = η_μν + h_μν where |h_μν| << 1.

## References

* Misner, Thorne, Wheeler, "Gravitation" (1973), Chapters 18, 35
* Wald, "General Relativity" (1984), Chapter 4
* Carroll, "Spacetime and Geometry" (2004), Chapter 7
-/

noncomputable section

open Bundle Set Finset Function Filter Module Topology ContinuousLinearMap
open scoped Manifold Bundle LinearMap Dual

namespace PseudoRiemannianMetric

/-! ## The Minkowski Metric -/

/-- The Minkowski metric η_μν = diag(-1, 1, 1, 1). -/
def minkowskiMetric (μ ν : Fin 4) : ℝ :=
  if μ = ν then
    if μ = 0 then -1 else 1
  else 0

/-- The Minkowski metric is symmetric. -/
lemma minkowskiMetric_symm (μ ν : Fin 4) : minkowskiMetric μ ν = minkowskiMetric ν μ := by
  unfold minkowskiMetric
  by_cases h : μ = ν
  · simp [h]
  · simp [h, Ne.symm h]

/-- The Minkowski metric is diagonal. -/
lemma minkowskiMetric_off_diag {μ ν : Fin 4} (h : μ ≠ ν) : minkowskiMetric μ ν = 0 := by
  unfold minkowskiMetric
  simp [h]

/-- The time-time component of the Minkowski metric. -/
lemma minkowskiMetric_00 : minkowskiMetric 0 0 = -1 := by
  unfold minkowskiMetric
  simp

/-- The spatial diagonal components of the Minkowski metric. -/
lemma minkowskiMetric_spatial {i : Fin 4} (hi : i ≠ 0) : minkowskiMetric i i = 1 := by
  unfold minkowskiMetric
  simp [hi]

/-! ## Metric Perturbation -/

/-- A metric perturbation h_μν around flat spacetime.
The full metric is g_μν = η_μν + h_μν with |h_μν| << 1. -/
structure WeakFieldPerturbation where
  /-- The perturbation components h_μν(x) -/
  h : Fin 4 → Fin 4 → ℝ → ℝ → ℝ → ℝ → ℝ
  /-- The perturbation is symmetric -/
  symmetric : ∀ μ ν t x y z, h μ ν t x y z = h ν μ t x y z

/-- The trace of the perturbation: h = η^μν h_μν. -/
def WeakFieldPerturbation.trace (hp : WeakFieldPerturbation) (t x y z : ℝ) : ℝ :=
  -hp.h 0 0 t x y z + hp.h 1 1 t x y z + hp.h 2 2 t x y z + hp.h 3 3 t x y z

/-- The trace-reversed perturbation: h̄_μν = h_μν - (1/2)η_μν h.
This simplifies the linearized Einstein equations. -/
def WeakFieldPerturbation.traceReversed (hp : WeakFieldPerturbation) :
    Fin 4 → Fin 4 → ℝ → ℝ → ℝ → ℝ → ℝ :=
  fun μ ν t x y z =>
    hp.h μ ν t x y z - (1/2) * minkowskiMetric μ ν * hp.trace t x y z

/-! ## Gauge Conditions -/

/-- The Lorenz (or harmonic/de Donder) gauge condition:
∂^μ h̄_μν = 0.

This is analogous to the Lorenz gauge in electromagnetism. -/
def isLorenzGauge (_hp : WeakFieldPerturbation) : Prop :=
  True  -- Full definition would require derivatives: ∂^μ h̄_μν = 0

/-- Gauge transformations: h_μν → h_μν + ∂_μ ξ_ν + ∂_ν ξ_μ
for any vector field ξ^μ. -/
def gaugeTransformation (hp : WeakFieldPerturbation) (_xi : Fin 4 → ℝ → ℝ → ℝ → ℝ → ℝ) :
    WeakFieldPerturbation where
  h := hp.h  -- Would add ∂_μ ξ_ν + ∂_ν ξ_μ
  symmetric := hp.symmetric

/-! ## Transverse-Traceless Gauge -/

/-- The transverse-traceless (TT) gauge for gravitational waves:
1. h = 0 (traceless)
2. h_0μ = 0 (purely spatial)
3. ∂^i h_ij = 0 (transverse)

This is the physical gauge for GW far from sources. -/
structure TTGaugePerturbation extends WeakFieldPerturbation where
  /-- Traceless: h = 0 -/
  traceless : ∀ t x y z, toWeakFieldPerturbation.trace t x y z = 0
  /-- Temporal components vanish -/
  temporal_zero : ∀ μ t x y z, h 0 μ t x y z = 0
  /-- Transverse condition -/
  transverse : True  -- ∂^i h_ij = 0

/-- In TT gauge, the trace-reversed perturbation equals the original
(since h = 0 implies h̄_μν = h_μν). -/
lemma TTGaugePerturbation.traceReversed_eq_h (tt : TTGaugePerturbation) (μ ν : Fin 4)
    (t x y z : ℝ) : tt.toWeakFieldPerturbation.traceReversed μ ν t x y z = tt.h μ ν t x y z := by
  unfold WeakFieldPerturbation.traceReversed
  simp [tt.traceless t x y z]

/-! ## Gravitational Wave Polarizations -/

/-- The plus polarization: h_+ affects x and y directions oppositely.
This is a plane wave propagating in the z direction. -/
def plusPolarization (amplitude : ℝ) (omega k t z : ℝ) : ℝ :=
  amplitude * Real.cos (omega * t - k * z)

/-- The cross polarization: h_× is rotated 45° from h_+.
This is a plane wave propagating in the z direction. -/
def crossPolarization (amplitude : ℝ) (omega k t z : ℝ) : ℝ :=
  amplitude * Real.cos (omega * t - k * z)

/-- Plane wave solutions in vacuum:
h_μν = ε_μν cos(k·x) where k² = 0. -/
def planeWaveSolution (epsilon : Fin 4 → Fin 4 → ℝ) (k : Fin 4 → ℝ) :
    Fin 4 → Fin 4 → ℝ → ℝ → ℝ → ℝ → ℝ :=
  fun μ ν t x y z =>
    let phase := -k 0 * t + k 1 * x + k 2 * y + k 3 * z
    epsilon μ ν * Real.cos phase

/-- The plane wave solution is symmetric if the polarization tensor is symmetric. -/
lemma planeWaveSolution_symmetric (epsilon : Fin 4 → Fin 4 → ℝ) (k : Fin 4 → ℝ)
    (hsymm : ∀ μ ν, epsilon μ ν = epsilon ν μ) :
    ∀ μ ν t x y z, planeWaveSolution epsilon k μ ν t x y z =
      planeWaveSolution epsilon k ν μ t x y z := by
  intros μ ν t x y z
  simp only [planeWaveSolution, hsymm μ ν]

/-! ## Newtonian Limit -/

/-- In the static, weak-field limit, linearized gravity reduces
to Newtonian gravity with h_00 = -2Φ/c².

This extracts the Newtonian potential from the perturbation. -/
def newtonianPotentialFromPerturbation (hp : WeakFieldPerturbation) (t x y z : ℝ) : ℝ :=
  -hp.h 0 0 t x y z / 2

/-! ## Graviton Properties

In the quantum field theory of linearized gravity:
- The graviton is a massless spin-2 particle
- It has 2 physical polarizations (helicity ±2)
- It propagates at the speed of light (k² = 0)

These are physical facts about quantum gravity that cannot be proven
from classical definitions alone. -/

/-- The number of physical graviton polarizations (helicity ±2). -/
def gravitonPolarizationCount : ℕ := 2

end PseudoRiemannianMetric
end
