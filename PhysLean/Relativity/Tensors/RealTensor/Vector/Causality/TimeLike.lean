/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Joseph Tooby-Smith
-/
import PhysLean.Relativity.Tensors.RealTensor.Vector.Causality.Basic

/-!

## Properties of time like vectors

-/

noncomputable section
namespace Lorentz
open realLorentzTensor
open InnerProductSpace
namespace Vector

/-- For timelike vectors with negative time components,
    their time components multiply to give a positive number -/
@[simp]
lemma timelike_neg_time_component_product {d : ℕ} (v w : Vector d)
    (hv_neg : v (Sum.inl 0) < 0) (hw_neg : w (Sum.inl 0) < 0) :
    v (Sum.inl 0) * w (Sum.inl 0) > 0 := by
  exact mul_pos_of_neg_of_neg hv_neg hw_neg

/-- For timelike vectors, the Minkowski inner product is positive -/
lemma timeLike_iff_norm_sq_pos {d : ℕ} (p : Vector d) :
    causalCharacter p = CausalCharacter.timeLike ↔ 0 < ⟪p, p⟫ₘ := by
  simp only [causalCharacter]
  split
  · rename_i h
    simp_all
  · split
    · rename_i h
      simp [h]
    · rename_i h
      simp_all

/-- For timeLike vectors in Minkowski space, the inner product of the spatial part
    is less than the square of the time component -/
lemma timelike_time_dominates_space {d : ℕ} {v : Vector d}
    (hv : causalCharacter v = .timeLike) :
    ⟪spatialPart v, spatialPart v⟫_ℝ < (timeComponent v) * (timeComponent v) := by
  rw [timeLike_iff_norm_sq_pos] at hv
  rw [minkowskiProduct_toCoord] at hv
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  have h_spatial_sum : ∑ x, spatialPart v x * spatialPart v x =
                    ∑ i, v (Sum.inr i) * v (Sum.inr i) := by
      simp only
  have h_time : timeComponent v = v (Sum.inl 0) := rfl
  rw [h_spatial_sum, h_time]
  have h_norm_pos : 0 < v (Sum.inl 0) * v (Sum.inl 0) -
                  ∑ i, v (Sum.inr i) * v (Sum.inr i) := hv
  -- Rearrange the inequality
  have h : ∑ i, v (Sum.inr i) * v (Sum.inr i) <
          v (Sum.inl 0) * v (Sum.inl 0) := by
    exact lt_of_sub_pos h_norm_pos
  exact h

/-- For future-directed timeLike vectors, the time component is positive. -/
lemma timelike_future_time_positive {d : ℕ} {v : Vector d}
    (_ : causalCharacter v = .timeLike) (hv_future : isFutureDirected v) :
    0 < timeComponent v := hv_future

/-- For future-directed timeLike vectors, the spatial norm is bounded by the time component. -/
lemma timelike_future_spatial_bound {d : ℕ} {v : Vector d}
    (hv : causalCharacter v = .timeLike) (hv_future : 0 < timeComponent v) :
    ‖spatialPart v‖ < timeComponent v := by
  have h := timelike_time_dominates_space hv
  rw [real_inner_self_eq_norm_sq] at h
  have h1 : ‖spatialPart v‖ ^ 2 < timeComponent v ^ 2 := by
    convert h using 2 ; ring
  have h2 : timeComponent v > 0 := hv_future
  have h3 : ‖spatialPart v‖ ≥ 0 := norm_nonneg _
  nlinarith [sq_nonneg (‖spatialPart v‖ - timeComponent v),
             sq_nonneg (‖spatialPart v‖ + timeComponent v)]

/-- For nonzero timelike vectors, the time component is nonzero -/
@[simp]
lemma time_component_ne_zero_of_timelike {d : ℕ} {v : Vector d}
    (hv : causalCharacter v = .timeLike) :
    v (Sum.inl 0) ≠ 0 := by
  by_contra h
  rw [timeLike_iff_norm_sq_pos] at hv
  rw [minkowskiProduct_toCoord] at hv
  simp at hv
  rw [h] at hv
  simp at hv
  have h_spatial_nonneg : 0 ≤ ∑ i, v (Sum.inr i) * v (Sum.inr i) :=
    Finset.sum_nonneg (fun i _ => mul_self_nonneg (v (Sum.inr i)))
  exact lt_irrefl 0 (h_spatial_nonneg.trans_lt hv)

/-- For timelike vectors, the time component is nonzero -/
lemma timelike_time_component_ne_zero {d : ℕ} {v : Vector d}
    (hv : causalCharacter v = .timeLike) :
    timeComponent v ≠ 0 := time_component_ne_zero_of_timelike hv

/-- A vector is timelike if and only if its time component squared is less than
    the sum of its spatial components squared -/
lemma timeLike_iff_time_lt_space {d : ℕ} {v : Vector d} :
    causalCharacter v = .timeLike ↔
    ⟪spatialPart v, spatialPart v⟫_ℝ < v (Sum.inl 0) * v (Sum.inl 0) := by
  constructor
  · intro h_timelike
    rw [timeLike_iff_norm_sq_pos, minkowskiProduct_toCoord] at h_timelike
    simp only [Fin.isValue, sub_pos] at h_timelike; exact h_timelike
  · intro h_time_lt_space
    rw [timeLike_iff_norm_sq_pos, minkowskiProduct_toCoord]
    simp only [Fin.isValue, sub_pos]
    exact h_time_lt_space

/-- Time component squared is positive for timelike vectors -/
@[simp]
lemma timeComponent_squared_pos_of_timelike {d : ℕ} {v : Vector d}
    (hv : causalCharacter v = .timeLike) :
    0 < (timeComponent v)^2 := by
  exact pow_two_pos_of_ne_zero (time_component_ne_zero_of_timelike hv)

/-- For timelike vectors, the spatial norm squared is strictly less
    than the time component squared -/
lemma timelike_spatial_lt_time_squared {d : ℕ} {v : Vector d}
    (hv : causalCharacter v = .timeLike) :
    ⟪spatialPart v, spatialPart v⟫_ℝ < (timeComponent v)^2 := by
  rw [timeLike_iff_norm_sq_pos, minkowskiProduct_toCoord] at hv
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  have h_time : timeComponent v = v (Sum.inl 0) := rfl
  simp [h_time, pow_two]
  have h_norm_pos : 0 < v (Sum.inl 0) * v (Sum.inl 0) -
                  ∑ i, v (Sum.inr i) * v (Sum.inr i) := hv
  exact lt_of_sub_pos h_norm_pos

/-- The reverse Cauchy-Schwarz inequality for future-directed timelike vectors.
    For future-directed timelike u, v: ⟪u, v⟫ₘ ≥ √(⟪u,u⟫ₘ) √(⟪v,v⟫ₘ) -/
lemma reverse_cauchy_schwarz {d : ℕ} (u v : Vector d)
    (hu_timelike : causalCharacter u = .timeLike)
    (hv_timelike : causalCharacter v = .timeLike)
    (hu_future : 0 < u (Sum.inl 0))
    (hv_future : 0 < v (Sum.inl 0)) :
    ⟪u, v⟫ₘ ≥ Real.sqrt ⟪u, u⟫ₘ * Real.sqrt ⟪v, v⟫ₘ := by
  have hu_pos : 0 < ⟪u, u⟫ₘ := (timeLike_iff_norm_sq_pos u).mp hu_timelike
  have hv_pos : 0 < ⟪v, v⟫ₘ := (timeLike_iff_norm_sq_pos v).mp hv_timelike
  have h_spatial_u := timelike_time_dominates_space hu_timelike
  have h_spatial_v := timelike_time_dominates_space hv_timelike
  have hu_spatial_bound : ‖spatialPart u‖ < timeComponent u := by
    have h := h_spatial_u
    rw [real_inner_self_eq_norm_sq] at h
    have h1 : ‖spatialPart u‖ ^ 2 < timeComponent u ^ 2 := by
      convert h using 2 ; ring
    have h2 : timeComponent u > 0 := hu_future
    have h3 : ‖spatialPart u‖ ≥ 0 := norm_nonneg _
    nlinarith [sq_nonneg (‖spatialPart u‖ - timeComponent u),
               sq_nonneg (‖spatialPart u‖ + timeComponent u)]
  have hv_spatial_bound : ‖spatialPart v‖ < timeComponent v := by
    have h := h_spatial_v
    rw [real_inner_self_eq_norm_sq] at h
    have h1 : ‖spatialPart v‖ ^ 2 < timeComponent v ^ 2 := by
      convert h using 2 ; ring
    have h2 : timeComponent v > 0 := hv_future
    have h3 : ‖spatialPart v‖ ≥ 0 := norm_nonneg _
    nlinarith [sq_nonneg (‖spatialPart v‖ - timeComponent v),
               sq_nonneg (‖spatialPart v‖ + timeComponent v)]
  have h_cs : @inner ℝ _ _ (spatialPart u) (spatialPart v) ≤ ‖spatialPart u‖ * ‖spatialPart v‖ :=
    real_inner_le_norm _ _
  rw [minkowskiProduct_eq_timeComponent_spatialPart]
  have h1 : timeComponent u * timeComponent v - @inner ℝ _ _ (spatialPart u) (spatialPart v) ≥
            timeComponent u * timeComponent v - ‖spatialPart u‖ * ‖spatialPart v‖ := by
    linarith
  have ha : timeComponent u > 0 := hu_future
  have hb : ‖spatialPart u‖ ≥ 0 := norm_nonneg _
  have hc : timeComponent v > 0 := hv_future
  have hd : ‖spatialPart v‖ ≥ 0 := norm_nonneg _
  have hab : timeComponent u > ‖spatialPart u‖ := hu_spatial_bound
  have hcd : timeComponent v > ‖spatialPart v‖ := hv_spatial_bound
  have h_norm_time_u : ‖timeComponent u‖ = timeComponent u := abs_of_pos ha
  have h_norm_time_v : ‖timeComponent v‖ = timeComponent v := abs_of_pos hc
  have h_ac_bd_pos : timeComponent u * timeComponent v - ‖spatialPart u‖ * ‖spatialPart v‖ > 0 := by
    have key : timeComponent u * timeComponent v > ‖spatialPart u‖ * ‖spatialPart v‖ := by
      have h1' : timeComponent u * timeComponent v > ‖spatialPart u‖ * timeComponent v := by
        have : (timeComponent u - ‖spatialPart u‖) * timeComponent v > 0 := by
          apply mul_pos
          · linarith
          · exact hc
        linarith
      have h2' : ‖spatialPart u‖ * timeComponent v ≥ ‖spatialPart u‖ * ‖spatialPart v‖ := by
        apply mul_le_mul_of_nonneg_left
        · linarith
        · exact hb
      linarith
    linarith
  calc Real.sqrt ⟪u, u⟫ₘ * Real.sqrt ⟪v, v⟫ₘ
      = Real.sqrt (⟪u, u⟫ₘ * ⟪v, v⟫ₘ) := by rw [Real.sqrt_mul (le_of_lt hu_pos)]
    _ = Real.sqrt ((‖timeComponent u‖ ^ 2 - ‖spatialPart u‖ ^ 2) *
          (‖timeComponent v‖ ^ 2 - ‖spatialPart v‖ ^ 2)) := by
        rw [minkowskiProduct_self_eq_timeComponent_spatialPart,
            minkowskiProduct_self_eq_timeComponent_spatialPart]
    _ = Real.sqrt ((timeComponent u ^ 2 - ‖spatialPart u‖ ^ 2) *
          (timeComponent v ^ 2 - ‖spatialPart v‖ ^ 2)) := by
        rw [h_norm_time_u, h_norm_time_v]
    _ ≤ timeComponent u * timeComponent v - ‖spatialPart u‖ * ‖spatialPart v‖ := by
        rw [Real.sqrt_le_left (le_of_lt h_ac_bd_pos)]
        have key : (timeComponent u ^ 2 - ‖spatialPart u‖ ^ 2) *
                   (timeComponent v ^ 2 - ‖spatialPart v‖ ^ 2) ≤
                   (timeComponent u * timeComponent v - ‖spatialPart u‖ * ‖spatialPart v‖) ^ 2 := by
          have h_sq : 0 ≤ (timeComponent u * ‖spatialPart v‖ -
                          ‖spatialPart u‖ * timeComponent v) ^ 2 := sq_nonneg _
          nlinarith [h_sq]
        exact key
    _ ≤ timeComponent u * timeComponent v - @inner ℝ _ _ (spatialPart u) (spatialPart v) := by
        linarith [h_cs]

/-- The reverse triangle inequality for future-directed timelike vectors.
    For future-directed timelike u, v with u + v also timelike:
    √⟪u + v, u + v⟫ₘ ≥ √⟪u, u⟫ₘ + √⟪v, v⟫ₘ -/
lemma reverse_triangle_ineq {d : ℕ} (u v : Vector d)
    (hu_timelike : causalCharacter u = .timeLike)
    (hv_timelike : causalCharacter v = .timeLike)
    (huv_timelike : causalCharacter (u + v) = .timeLike)
    (hu_future : 0 < u (Sum.inl 0))
    (hv_future : 0 < v (Sum.inl 0)) :
    Real.sqrt ⟪u + v, u + v⟫ₘ ≥ Real.sqrt ⟪u, u⟫ₘ + Real.sqrt ⟪v, v⟫ₘ := by
  have hu_pos : 0 < ⟪u, u⟫ₘ := (timeLike_iff_norm_sq_pos u).mp hu_timelike
  have hv_pos : 0 < ⟪v, v⟫ₘ := (timeLike_iff_norm_sq_pos v).mp hv_timelike
  have huv_pos : 0 < ⟪u + v, u + v⟫ₘ := (timeLike_iff_norm_sq_pos (u + v)).mp huv_timelike
  have h_rcs := reverse_cauchy_schwarz u v hu_timelike hv_timelike hu_future hv_future
  have h_expand : ⟪u + v, u + v⟫ₘ = ⟪u, u⟫ₘ + 2 * ⟪u, v⟫ₘ + ⟪v, v⟫ₘ := by
    simp only [minkowskiProduct_apply, minkowskiProductMap_add_snd, minkowskiProductMap_symm]
    ring
  have h_bound : ⟪u + v, u + v⟫ₘ ≥ (Real.sqrt ⟪u, u⟫ₘ + Real.sqrt ⟪v, v⟫ₘ) ^ 2 := by
    rw [h_expand, add_sq, Real.sq_sqrt (le_of_lt hu_pos), Real.sq_sqrt (le_of_lt hv_pos)]
    have h2 : 2 * ⟪u, v⟫ₘ ≥ 2 * Real.sqrt ⟪u, u⟫ₘ * Real.sqrt ⟪v, v⟫ₘ := by
      have := h_rcs
      linarith
    linarith
  have h_sqrt_pos : Real.sqrt ⟪u, u⟫ₘ + Real.sqrt ⟪v, v⟫ₘ > 0 := by
    have := Real.sqrt_pos.mpr hu_pos
    have := Real.sqrt_pos.mpr hv_pos
    linarith
  calc Real.sqrt ⟪u + v, u + v⟫ₘ ≥ Real.sqrt ((Real.sqrt ⟪u, u⟫ₘ + Real.sqrt ⟪v, v⟫ₘ) ^ 2) :=
      Real.sqrt_le_sqrt h_bound
    _ = |Real.sqrt ⟪u, u⟫ₘ + Real.sqrt ⟪v, v⟫ₘ| := Real.sqrt_sq_eq_abs _
    _ = Real.sqrt ⟪u, u⟫ₘ + Real.sqrt ⟪v, v⟫ₘ := abs_of_pos h_sqrt_pos

end Vector
end Lorentz
