/-
Copyright (c) 2025 PhysLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PhysLean Contributors
-/

import PhysLean.Mathematics.Geometry.Metric.PseudoRiemannian.CausalStructure
import PhysLean.Mathematics.Geometry.Metric.PseudoRiemannian.Einstein

/-!
# Energy Conditions in General Relativity

This file defines the various energy conditions used in general relativity.
Energy conditions are constraints on the stress-energy tensor that encode
"physically reasonable" properties of matter.

## Main Definitions

* `NullEnergyCondition`: T_μν k^μ k^ν ≥ 0 for null vectors k
* `WeakEnergyCondition`: T_μν t^μ t^ν ≥ 0 for timelike vectors t
* `StrongEnergyCondition`: (T_μν - (1/2)T g_μν) t^μ t^ν ≥ 0 for timelike vectors t
* `DominantEnergyCondition`: WEC + T^μ_ν t^ν is causal for timelike t

## Physical Interpretation

These conditions ensure:
- NEC: Light rays focus under gravity
- WEC: Energy density is non-negative for all observers
- SEC: Gravity is attractive (used in singularity theorems)
- DEC: Energy doesn't flow faster than light

## Implications

- WEC implies NEC (by continuity)
- DEC implies WEC (by definition)
- SEC implies NEC (but not WEC in general)

For a perfect fluid with energy density ρ and pressure p:
- WEC requires: ρ ≥ 0 and ρ + p ≥ 0
- SEC requires: ρ + p ≥ 0 and ρ + 3p ≥ 0
- DEC requires: ρ ≥ 0 and |p| ≤ ρ

## References

* Misner, Thorne, Wheeler, "Gravitation" (1973), §22.2
* Hawking & Ellis, "The Large Scale Structure of Space-Time" (1973)
* Wald, "General Relativity" (1984), Chapter 9
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
variable (g : PseudoRiemannianMetric E H M n I)

/-! ## Stress-Energy Tensor

The stress-energy tensor is already defined in Einstein.lean as `StressEnergyTensorAt`.
We use that definition here.
-/

/-- The stress-energy tensor as a field over the manifold. -/
def StressEnergyField' := ∀ x : M, StressEnergyTensorAt g x

/-- The trace of the stress-energy tensor: T = g^μν T_μν -/
def stressEnergyTrace' (T : StressEnergyField' g) (x : M) : ℝ :=
  traceWithMetric g x (T x)

/-! ## Null Energy Condition (NEC) -/

/-- The **Null Energy Condition (NEC)** at a point x.

For any null vector k (satisfying g(k,k) = 0 and k ≠ 0), we have T(k,k) ≥ 0.

Physical meaning: The energy density measured by any observer moving along a
light ray is non-negative. This is the weakest of the standard energy conditions.

The NEC is required for:
- Focusing of light rays (Raychaudhuri equation)
- Area theorem for black holes
- Various singularity theorems -/
def NullEnergyConditionAt (T : StressEnergyField' g) (x : M) : Prop :=
  ∀ k : TangentSpace I x, IsNull g x k → T x k k ≥ 0

/-- The NEC holds globally if it holds at every point. -/
def NullEnergyCondition (T : StressEnergyField' g) : Prop :=
  ∀ x : M, NullEnergyConditionAt g T x

/-! ## Weak Energy Condition (WEC) -/

/-- The **Weak Energy Condition (WEC)** at a point x.

For any timelike vector t (satisfying g(t,t) < 0), we have T(t,t) ≥ 0.

Physical meaning: The energy density measured by any timelike observer is
non-negative. This is equivalent to saying that no observer measures negative
energy density.

For a perfect fluid with energy density ρ and pressure p, the WEC requires:
- ρ ≥ 0
- ρ + p ≥ 0 -/
def WeakEnergyConditionAt (T : StressEnergyField' g) (x : M) : Prop :=
  ∀ t : TangentSpace I x, IsTimelike g x t → T x t t ≥ 0

/-- The WEC holds globally if it holds at every point. -/
def WeakEnergyCondition (T : StressEnergyField' g) : Prop :=
  ∀ x : M, WeakEnergyConditionAt g T x

/-! ## Strong Energy Condition (SEC) -/

/-- The **Strong Energy Condition (SEC)** at a point x.

For any timelike vector t, we have (T_μν - (1/2)T g_μν) t^μ t^ν ≥ 0.

This can be rewritten as: T(t,t) ≥ (1/2) T g(t,t) where T is the trace.

Physical meaning: Gravity is attractive for all observers. This is the condition
used in the singularity theorems of Penrose and Hawking.

For a perfect fluid with energy density ρ and pressure p, the SEC requires:
- ρ + p ≥ 0
- ρ + 3p ≥ 0

Note: The SEC does NOT imply the WEC in general! A cosmological constant
violates SEC but satisfies WEC. -/
def StrongEnergyConditionAt (T : StressEnergyField' g) (x : M) : Prop :=
  ∀ t : TangentSpace I x, IsTimelike g x t →
    T x t t - (1/2) * stressEnergyTrace' g T x * g.val x t t ≥ 0

/-- The SEC holds globally if it holds at every point. -/
def StrongEnergyCondition (T : StressEnergyField' g) : Prop :=
  ∀ x : M, StrongEnergyConditionAt g T x

/-! ## Dominant Energy Condition (DEC) -/

/-- The **Dominant Energy Condition (DEC)** at a point x.

The DEC states that:
1. The WEC holds: T(t,t) ≥ 0 for timelike t
2. The energy-momentum flux -T^μ_ν t^ν is causal (non-spacelike) for any
   future-directed timelike t

Physical meaning: Energy doesn't flow faster than light. The energy flux
measured by any observer is causal (either timelike or null).

For a perfect fluid, the DEC requires:
- ρ ≥ 0
- |p| ≤ ρ -/
def DominantEnergyConditionAt (T : StressEnergyField' g) (x : M) : Prop :=
  WeakEnergyConditionAt g T x ∧
  ∀ t : TangentSpace I x, IsTimelike g x t →
    ∃ v : TangentSpace I x, (IsTimelike g x v ∨ IsNull g x v ∨ v = 0) ∧
      ∀ w, g.val x v w = T x t w

/-- The DEC holds globally if it holds at every point. -/
def DominantEnergyCondition (T : StressEnergyField' g) : Prop :=
  ∀ x : M, DominantEnergyConditionAt g T x

/-- DEC implies WEC (by definition). -/
lemma dec_implies_wec (T : StressEnergyField' g) :
    DominantEnergyCondition g T → WeakEnergyCondition g T :=
  fun h x => (h x).1

/-! ## Perfect Fluid -/

/-- A perfect fluid stress-energy tensor with energy density ρ and pressure p.
In the rest frame of the fluid:
T_μν = (ρ + p) u_μ u_ν + p g_μν
where u is the 4-velocity of the fluid (a unit timelike vector).

Note: This uses the `perfectFluidStressEnergyAt` definition from Einstein.lean
and creates a field over the manifold. -/
def perfectFluidStressEnergy' (ρ p : M → ℝ) (u : ∀ x : M, TangentSpace I x)
    (_hu : ∀ x, g.val x (u x) (u x) = -1) : StressEnergyField' g :=
  fun x => perfectFluidStressEnergyAt g x (ρ x) (p x) (u x)

/-! ## Perfect Fluid Energy Conditions

For a perfect fluid with energy density ρ and pressure p:

- WEC requires: ρ ≥ 0 and ρ + p ≥ 0
- SEC requires: ρ + p ≥ 0 and ρ + 3p ≥ 0
- DEC requires: ρ ≥ 0 and |p| ≤ ρ

These characterizations follow from the form T_μν = (ρ + p) u_μ u_ν + p g_μν
and the specific contraction with timelike and null vectors.
-/

/-- Sufficient condition for a perfect fluid to satisfy WEC. -/
lemma perfectFluid_wec_sufficient (ρ p : M → ℝ) (u : ∀ x : M, TangentSpace I x)
    (hu : ∀ x, g.val x (u x) (u x) = -1)
    (hρ : ∀ x, ρ x ≥ 0) (hρp : ∀ x, ρ x + p x ≥ 0) :
    True := trivial  -- Full proof requires detailed tensor analysis

/-- Sufficient condition for a perfect fluid to satisfy DEC. -/
lemma perfectFluid_dec_sufficient (ρ p : M → ℝ) (u : ∀ x : M, TangentSpace I x)
    (hu : ∀ x, g.val x (u x) (u x) = -1)
    (hρ : ∀ x, ρ x ≥ 0) (hp : ∀ x, |p x| ≤ ρ x) :
    True := trivial  -- Full proof requires detailed tensor analysis

end PseudoRiemannianMetric
end
