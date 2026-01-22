/-
Copyright (c) 2025 PhysLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PhysLean Contributors
-/

import PhysLean.Mathematics.Geometry.Metric.PseudoRiemannian.Defs

/-!
# Causal Structure on Pseudo-Riemannian Manifolds

This file defines the causal structure of a pseudo-Riemannian manifold, classifying
tangent vectors based on the sign of the metric applied to them.

## Main Definitions

* `PseudoRiemannianMetric.IsTimelike`: A vector `v` is timelike if `g(v,v) < 0`.
* `PseudoRiemannianMetric.IsSpacelike`: A vector `v` is spacelike if `g(v,v) > 0`.
* `PseudoRiemannianMetric.IsNull`: A vector `v` is null (lightlike) if `g(v,v) = 0` and `v ≠ 0`.
* `PseudoRiemannianMetric.IsCausal`: A vector is causal if it is timelike or null.

## References

* Misner, Thorne, Wheeler, "Gravitation" (1973), Chapter 2
* O'Neill, "Semi-Riemannian Geometry" (1983), Chapter 5
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

/-! ## Causal Character of Vectors -/

/-- A tangent vector `v` at point `x` is **timelike** if `g(v, v) < 0`.
In general relativity with signature `(-,+,+,+)`, timelike vectors represent
directions that can be traveled by massive particles. -/
def IsTimelike (x : M) (v : TangentSpace I x) : Prop :=
  g.val x v v < 0

/-- A tangent vector `v` at point `x` is **spacelike** if `g(v, v) > 0`.
In general relativity, spacelike vectors represent purely spatial directions. -/
def IsSpacelike (x : M) (v : TangentSpace I x) : Prop :=
  g.val x v v > 0

/-- A tangent vector `v` at point `x` is **null** (or lightlike) if `g(v, v) = 0` and `v ≠ 0`.
Null vectors represent directions traveled by massless particles (like photons). -/
def IsNull (x : M) (v : TangentSpace I x) : Prop :=
  g.val x v v = 0 ∧ v ≠ 0

/-- A tangent vector is **causal** if it is either timelike or null.
Causal vectors represent possible directions of propagation for physical signals. -/
def IsCausal (x : M) (v : TangentSpace I x) : Prop :=
  IsTimelike g x v ∨ IsNull g x v

/-! ## Basic Properties -/

/-- The zero vector is not timelike. -/
lemma not_isTimelike_zero (x : M) : ¬IsTimelike g x 0 := by
  simp only [IsTimelike, map_zero, lt_irrefl, not_false_eq_true]

/-- The zero vector is not spacelike. -/
lemma not_isSpacelike_zero (x : M) : ¬IsSpacelike g x 0 := by
  simp only [IsSpacelike, map_zero, lt_irrefl, not_false_eq_true]

/-- The zero vector is not null (by definition, null requires v ≠ 0). -/
lemma not_isNull_zero (x : M) : ¬IsNull g x 0 := by
  simp only [IsNull, ne_eq, not_true_eq_false, and_false, not_false_eq_true]

/-- The zero vector is not causal. -/
lemma not_isCausal_zero (x : M) : ¬IsCausal g x 0 := by
  simp only [IsCausal, not_isTimelike_zero, not_isNull_zero, or_self, not_false_eq_true]

/-- A vector cannot be both timelike and spacelike. -/
lemma not_timelike_and_spacelike (x : M) (v : TangentSpace I x) :
    ¬(IsTimelike g x v ∧ IsSpacelike g x v) := by
  intro ⟨ht, hs⟩
  exact lt_asymm ht hs

/-- A vector cannot be both timelike and null. -/
lemma not_timelike_and_null (x : M) (v : TangentSpace I x) :
    ¬(IsTimelike g x v ∧ IsNull g x v) := by
  intro ⟨ht, hn⟩
  simp only [IsTimelike, IsNull] at ht hn
  rw [hn.1] at ht
  exact lt_irrefl 0 ht

/-- A vector cannot be both spacelike and null. -/
lemma not_spacelike_and_null (x : M) (v : TangentSpace I x) :
    ¬(IsSpacelike g x v ∧ IsNull g x v) := by
  intro ⟨hs, hn⟩
  simp only [IsSpacelike, IsNull] at hs hn
  rw [hn.1] at hs
  exact lt_irrefl 0 hs

/-- A nonzero vector has exactly one causal character: timelike, spacelike, or null. -/
lemma trichotomy (x : M) (v : TangentSpace I x) (hv : v ≠ 0) :
    IsTimelike g x v ∨ IsSpacelike g x v ∨ IsNull g x v := by
  rcases lt_trichotomy (g.val x v v) 0 with h | h | h
  · left; exact h
  · right; right; exact ⟨h, hv⟩
  · right; left; exact h

/-- Scaling a timelike vector by a nonzero scalar preserves timelikeness. -/
lemma isTimelike_smul (x : M) (v : TangentSpace I x) (c : ℝ) (hc : c ≠ 0)
    (hv : IsTimelike g x v) : IsTimelike g x (c • v) := by
  simp only [IsTimelike, ContinuousLinearMap.map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  have hc2 : c * c > 0 := mul_self_pos.mpr hc
  calc c * (c * g.val x v v) = c * c * g.val x v v := by ring
    _ < 0 := mul_neg_of_pos_of_neg hc2 hv

/-- Scaling a spacelike vector by a nonzero scalar preserves spacelikeness. -/
lemma isSpacelike_smul (x : M) (v : TangentSpace I x) (c : ℝ) (hc : c ≠ 0)
    (hv : IsSpacelike g x v) : IsSpacelike g x (c • v) := by
  simp only [IsSpacelike, ContinuousLinearMap.map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  have hc2 : c * c > 0 := mul_self_pos.mpr hc
  calc c * (c * g.val x v v) = c * c * g.val x v v := by ring
    _ > 0 := mul_pos hc2 hv

/-- Scaling a null vector by a nonzero scalar preserves nullness. -/
lemma isNull_smul (x : M) (v : TangentSpace I x) (c : ℝ) (hc : c ≠ 0)
    (hv : IsNull g x v) : IsNull g x (c • v) := by
  simp only [IsNull] at hv ⊢
  constructor
  · simp only [ContinuousLinearMap.map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [hv.1]
    ring
  · simp only [ne_eq, smul_eq_zero, hc, false_or]
    exact hv.2

/-- Timelike vectors are causal. -/
lemma IsTimelike.isCausal {x : M} {v : TangentSpace I x} (hv : IsTimelike g x v) :
    IsCausal g x v :=
  Or.inl hv

/-- Null vectors are causal. -/
lemma IsNull.isCausal {x : M} {v : TangentSpace I x} (hv : IsNull g x v) :
    IsCausal g x v :=
  Or.inr hv

/-- A nonzero vector is spacelike iff it is not causal. -/
lemma isSpacelike_iff_not_causal (x : M) (v : TangentSpace I x) (hv : v ≠ 0) :
    IsSpacelike g x v ↔ ¬IsCausal g x v := by
  constructor
  · intro hs hc
    cases hc with
    | inl ht => exact not_timelike_and_spacelike g x v ⟨ht, hs⟩
    | inr hn => exact not_spacelike_and_null g x v ⟨hs, hn⟩
  · intro hnc
    rcases trichotomy g x v hv with ht | hs | hn
    · exact absurd (IsTimelike.isCausal g ht) hnc
    · exact hs
    · exact absurd (IsNull.isCausal g hn) hnc

/-! ## Causal Character Predicates -/

/-- The squared norm of a vector under the metric. -/
def normSq (x : M) (v : TangentSpace I x) : ℝ :=
  g.val x v v

lemma isTimelike_iff_normSq_neg (x : M) (v : TangentSpace I x) :
    IsTimelike g x v ↔ normSq g x v < 0 := Iff.rfl

lemma isSpacelike_iff_normSq_pos (x : M) (v : TangentSpace I x) :
    IsSpacelike g x v ↔ normSq g x v > 0 := Iff.rfl

lemma isNull_iff_normSq_zero_and_nonzero (x : M) (v : TangentSpace I x) :
    IsNull g x v ↔ normSq g x v = 0 ∧ v ≠ 0 := Iff.rfl

end PseudoRiemannianMetric
end
