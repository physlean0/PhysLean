/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Joseph Tooby-Smith
-/
import PhysLean.StatisticalMechanics.CanonicalEnsemble.Finite
import PhysLean.Meta.Informal.Basic
/-!

# Two-state canonical ensemble

This module contains the definitions and properties related to the two-state
canonical ensemble.

-/

namespace CanonicalEnsemble

open Temperature
open Real MeasureTheory

/-- The canonical ensemble corresponding to state system, with one state of energy
  `E₀` and the other state of energy `E₁`. -/
noncomputable def twoState (E₀ E₁ : ℝ) : CanonicalEnsemble (Fin 2) where
  energy := fun | 0 => E₀ | 1 => E₁
  dof := 0
  μ := Measure.count
  energy_measurable := by fun_prop

instance {E₀ E₁} : IsFinite (twoState E₀ E₁) where
  μ_eq_count := rfl
  dof_eq_zero := rfl
  phase_space_unit_eq_one := rfl

lemma twoState_partitionFunction_apply (E₀ E₁ : ℝ) (T : Temperature) :
    (twoState E₀ E₁).partitionFunction T = exp (- β T * E₀) + exp (- β T * E₁) := by
  rw [partitionFunction_of_fintype, twoState]
  simp [Fin.sum_univ_two]

lemma twoState_partitionFunction_apply_eq_cosh (E₀ E₁ : ℝ) (T : Temperature) :
    (twoState E₀ E₁).partitionFunction T =
    2 * exp (- β T * (E₀ + E₁) / 2) * cosh (β T * (E₁ - E₀) / 2) := by
  rw [twoState_partitionFunction_apply, Real.cosh_eq]
  field_simp
  simp only [mul_add, ← exp_add]
  ring_nf

@[simp]
lemma twoState_energy_fst (E₀ E₁ : ℝ) : (twoState E₀ E₁).energy 0 = E₀ := by
  rfl

@[simp]
lemma twoState_energy_snd (E₀ E₁ : ℝ) : (twoState E₀ E₁).energy 1 = E₁ := by
  rfl

/-- Probability of the first state (energy `E₀`) in closed form. -/
lemma twoState_probability_fst (E₀ E₁ : ℝ) (T : Temperature) :
    (twoState E₀ E₁).probability T 0 = 1 / 2 * (1 + Real.tanh (β T * (E₁ - E₀) / 2)) := by
  set x := β T * (E₁ - E₀) / 2
  set C := β T * (E₀ + E₁) / 2
  have hE0 : - β T * E₀ = x - C := by
    simp [x, C]; ring
  have hE1 : - β T * E₁ = -x - C := by
    simp [x, C]; ring
  rw [probability, mathematicalPartitionFunction_of_fintype]
  simp only [twoState, Fin.sum_univ_two, Fin.isValue]
  rw [hE0, hE1]
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
  simp only [Real.exp_sub, Real.exp_neg]
  field_simp
  ring

/-- Probability of the second state (energy `E₁`) in closed form. -/
lemma twoState_probability_snd (E₀ E₁ : ℝ) (T : Temperature) :
    (twoState E₀ E₁).probability T 1 = 1 / 2 * (1 - Real.tanh (β T * (E₁ - E₀) / 2)) := by
  set x := β T * (E₁ - E₀) / 2
  set C := β T * (E₀ + E₁) / 2
  have hE0 : - β T * E₀ = x - C := by
    simp [x, C]; ring
  have hE1 : - β T * E₁ = -x - C := by
    simp [x, C]; ring
  rw [probability, mathematicalPartitionFunction_of_fintype]
  simp only [twoState, Fin.sum_univ_two, Fin.isValue]
  rw [hE0, hE1]
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
  simp only [Real.exp_sub, Real.exp_neg]
  field_simp
  ring

lemma twoState_meanEnergy_eq (E₀ E₁ : ℝ) (T : Temperature) :
    (twoState E₀ E₁).meanEnergy T =
    (E₀ + E₁) / 2 - (E₁ - E₀) / 2 * Real.tanh (β T * (E₁ - E₀) / 2) := by
  rw [meanEnergy_of_fintype]
  simp [Fin.sum_univ_two, twoState_probability_fst, twoState_probability_snd]
  ring

/-- The Helmholtz free energy of the two-state canonical ensemble in closed form.

Using the partition function Z = exp(-βE₀) + exp(-βE₁), we have:
  F = -k_B T log Z = -k_B T log(exp(-βE₀) + exp(-βE₁)) -/
lemma twoState_helmholtzFreeEnergy_eq (E₀ E₁ : ℝ) (T : Temperature) :
    (twoState E₀ E₁).helmholtzFreeEnergy T =
    -Constants.kB * T.val * Real.log (exp (- β T * E₀) + exp (- β T * E₁)) := by
  simp only [helmholtzFreeEnergy]
  rw [twoState_partitionFunction_apply]

/-- The Helmholtz free energy of the two-state canonical ensemble expressed using hyperbolic cosine.

This equivalent formulation expresses F in terms of the average energy (E₀+E₁)/2
and the energy splitting via cosh:
  F = (E₀+E₁)/2 - k_B T log(2) - k_B T log(cosh(β(E₁-E₀)/2)) -/
lemma twoState_helmholtzFreeEnergy_eq_cosh (E₀ E₁ : ℝ) (T : Temperature) (hT : 0 < T.val) :
    (twoState E₀ E₁).helmholtzFreeEnergy T =
    (E₀ + E₁) / 2 -
      Constants.kB * T.val * (Real.log 2 + Real.log (cosh (β T * (E₁ - E₀) / 2))) := by
  rw [twoState_helmholtzFreeEnergy_eq]
  have h1 : 0 < (2 : ℝ) := by norm_num
  have h2 : 0 < exp (- β T * (E₀ + E₁) / 2) := exp_pos _
  have h3 : 0 < cosh (β T * (E₁ - E₀) / 2) := cosh_pos _
  have heq : exp (- β T * E₀) + exp (- β T * E₁) =
             2 * (exp (- β T * (E₀ + E₁) / 2) * cosh (β T * (E₁ - E₀) / 2)) := by
    rw [Real.cosh_eq]
    field_simp
    simp only [mul_add, ← exp_add]
    ring_nf
  rw [heq]
  rw [Real.log_mul (by linarith : (2 : ℝ) ≠ 0) (mul_pos h2 h3).ne']
  rw [Real.log_mul h2.ne' h3.ne']
  rw [Real.log_exp]
  have hkB_ne : Constants.kB ≠ 0 := Constants.kB_neq_zero
  have hT_ne : (T.val : ℝ) ≠ 0 := (NNReal.coe_pos.mpr hT).ne'
  -- β T : ℝ≥0, and (β T : ℝ) = 1 / (kB * T.val)
  have hβ_eq : (β T : ℝ) = 1 / (Constants.kB * T.val) := rfl
  rw [hβ_eq]
  field_simp [hkB_ne, hT_ne]
  ring

/-- The Shannon entropy of the two-state canonical ensemble in closed form.

The entropy is given by S = k_B * [log(2 * cosh(x)) - x * tanh(x)] where x = β(E₁ - E₀)/2.

This can be derived from the thermodynamic relation S = (U - F)/T, or directly from the
Shannon entropy formula S = -k_B ∑ᵢ pᵢ log(pᵢ). -/
lemma twoState_shannonEntropy_eq (E₀ E₁ : ℝ) (T : Temperature) (_ : 0 < T.val) :
    (twoState E₀ E₁).shannonEntropy T =
    Constants.kB * (Real.log (2 * cosh (β T * (E₁ - E₀) / 2)) -
                     β T * (E₁ - E₀) / 2 * Real.tanh (β T * (E₁ - E₀) / 2)) := by
  set x := β T * (E₁ - E₀) / 2
  rw [shannonEntropy, Fin.sum_univ_two]
  simp only [twoState_probability_fst, twoState_probability_snd]
  set p₀ := (1 : ℝ) / 2 * (1 + Real.tanh x)
  set p₁ := (1 : ℝ) / 2 * (1 - Real.tanh x)
  -- Prove |tanh x| < 1 from the definition: tanh = sinh/cosh and cosh² - sinh² = 1
  have hcosh_pos : 0 < cosh x := cosh_pos x
  have htanh_lt_one : Real.tanh x < 1 := by
    rw [Real.tanh_eq_sinh_div_cosh]
    have hsinh_lt : sinh x < cosh x := sinh_lt_cosh x
    rw [div_lt_one hcosh_pos]
    exact hsinh_lt
  have hneg_one_lt_tanh : -1 < Real.tanh x := by
    rw [Real.tanh_eq_sinh_div_cosh]
    -- -cosh < sinh  ⟺  0 < cosh + sinh = exp(x) > 0
    have h_sum_pos : 0 < cosh x + sinh x := by
      rw [Real.cosh_eq, Real.sinh_eq]
      have : (exp x + exp (-x)) / 2 + (exp x - exp (-x)) / 2 = exp x := by ring
      rw [this]
      exact exp_pos x
    rw [lt_div_iff₀ hcosh_pos, neg_one_mul]
    linarith
  have h1_plus_tanh_pos : 0 < 1 + Real.tanh x := by linarith
  have h1_minus_tanh_pos : 0 < 1 - Real.tanh x := by linarith
  have hp₀_pos : 0 < p₀ := by
    show 0 < 1 / 2 * (1 + Real.tanh x)
    positivity
  have hp₁_pos : 0 < p₁ := by
    show 0 < 1 / 2 * (1 - Real.tanh x)
    positivity
  have hp_sum : p₀ + p₁ = 1 := by ring
  -- Use the identity for binary entropy in terms of tanh
  have h2cosh_pos : 0 < 2 * cosh x := by linarith
  -- log(p₀) = log(1/2) + log(1 + tanh(x)) = log((1 + tanh(x))/2)
  -- For cosh(x) > 0: 1 + tanh(x) = (cosh(x) + sinh(x))/cosh(x) = exp(x)/cosh(x)
  have h1_plus_tanh : 1 + Real.tanh x = exp x / cosh x := by
    rw [Real.tanh_eq_sinh_div_cosh, Real.cosh_eq, Real.sinh_eq]
    field_simp
    ring
  have h1_minus_tanh : 1 - Real.tanh x = exp (-x) / cosh x := by
    rw [Real.tanh_eq_sinh_div_cosh, Real.cosh_eq, Real.sinh_eq]
    field_simp
    ring
  -- So p₀ = exp(x) / (2 * cosh(x)) and p₁ = exp(-x) / (2 * cosh(x))
  have hp₀_eq : p₀ = exp x / (2 * cosh x) := by
    simp only [p₀, h1_plus_tanh]
    field_simp
  have hp₁_eq : p₁ = exp (-x) / (2 * cosh x) := by
    simp only [p₁, h1_minus_tanh]
    field_simp
  -- log(p₀) = x - log(2 * cosh(x))
  have hlog_p₀ : Real.log p₀ = x - Real.log (2 * cosh x) := by
    rw [hp₀_eq, Real.log_div (exp_pos x).ne' h2cosh_pos.ne', Real.log_exp]
  -- log(p₁) = -x - log(2 * cosh(x))
  have hlog_p₁ : Real.log p₁ = -x - Real.log (2 * cosh x) := by
    rw [hp₁_eq, Real.log_div (exp_pos (-x)).ne' h2cosh_pos.ne', Real.log_exp]
  -- S = -kB * (p₀ * log(p₀) + p₁ * log(p₁))
  --   = kB * (log(2cosh) - x * tanh(x))
  have hp₀_minus_p₁ : p₀ - p₁ = Real.tanh x := by ring
  calc -Constants.kB * (p₀ * Real.log p₀ + p₁ * Real.log p₁)
      = -Constants.kB * (p₀ * (x - Real.log (2 * cosh x)) + p₁ * (-x - Real.log (2 * cosh x))) := by
        rw [hlog_p₀, hlog_p₁]
    _ = -Constants.kB * ((p₀ - p₁) * x - (p₀ + p₁) * Real.log (2 * cosh x)) := by ring
    _ = -Constants.kB * (Real.tanh x * x - 1 * Real.log (2 * cosh x)) := by
        rw [hp₀_minus_p₁, hp_sum]
    _ = Constants.kB * (Real.log (2 * cosh x) - x * Real.tanh x) := by ring

end CanonicalEnsemble
