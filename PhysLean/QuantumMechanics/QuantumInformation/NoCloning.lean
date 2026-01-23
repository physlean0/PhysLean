/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.QuantumMechanics.QuantumInformation.Qubit
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.InnerProductSpace.Adjoint
/-!

# The No-Cloning Theorem

The no-cloning theorem is a fundamental result in quantum information theory stating that
it is impossible to create an independent and identical copy of an arbitrary unknown quantum state.

## Main results

* `cloning_inner_product_constraint` : If a linear isometry clones two states, then their
  inner product must equal its own square: ⟨ψ|φ⟩ = ⟨ψ|φ⟩². This implies ⟨ψ|φ⟩ ∈ {0, 1}.

* `no_cloning_theorem` : There is no inner-product-preserving linear map that can clone
  two non-orthogonal, non-identical normalized states.

## The Physics

The no-cloning theorem follows from the linearity (or unitarity) of quantum mechanics.
If a cloning operation U existed such that:
  U(|ψ⟩ ⊗ |blank⟩) = |ψ⟩ ⊗ |ψ⟩

Then for any two states |ψ⟩ and |φ⟩:
  ⟨ψ|φ⟩ = ⟨ψ,blank|U†U|φ,blank⟩ = ⟨ψ,ψ|φ,φ⟩ = ⟨ψ|φ⟩ · ⟨ψ|φ⟩ = ⟨ψ|φ⟩²

This implies ⟨ψ|φ⟩ ∈ {0, 1}, meaning cloning is only possible for orthogonal or identical states.

-/

namespace QuantumMechanics

namespace QuantumInformation

open scoped TensorProduct

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-!
## The core no-cloning constraint

We first prove that if a linear map "clones" two states (in the sense that it maps
|ψ⟩ ⊗ |e⟩ to |ψ⟩ ⊗ |ψ⟩), then the inner product of those states must satisfy
⟨ψ|φ⟩ = ⟨ψ|φ⟩².
-/

/-- A cloning map for a state ψ with blank state e is a linear map that sends ψ ⊗ e to ψ ⊗ ψ. -/
def ClonesState (U : H ⊗[𝕜] H →ₗ[𝕜] H ⊗[𝕜] H) (e : H) (ψ : H) : Prop :=
  U (ψ ⊗ₜ e) = ψ ⊗ₜ ψ

/-- If an inner-product-preserving linear map clones two states ψ and φ (both using the same
blank state e), then ⟨ψ|φ⟩ * ⟨e|e⟩ = ⟨ψ|φ⟩².

This is the key lemma for the no-cloning theorem. -/
theorem cloning_inner_product_constraint
    (U : H ⊗[𝕜] H →ₗᵢ[𝕜] H ⊗[𝕜] H) (e ψ φ : H)
    (hψ : ClonesState U.toLinearMap e ψ) (hφ : ClonesState U.toLinearMap e φ) :
    @inner 𝕜 _ _ ψ φ * @inner 𝕜 _ _ e e = (@inner 𝕜 _ _ ψ φ : 𝕜) * @inner 𝕜 _ _ ψ φ := by
  -- The key insight: U preserves inner products
  have h : @inner 𝕜 _ _ (U (ψ ⊗ₜ e)) (U (φ ⊗ₜ e)) = @inner 𝕜 _ _ (ψ ⊗ₜ e) (φ ⊗ₜ e) :=
    U.inner_map_map (ψ ⊗ₜ e) (φ ⊗ₜ e)
  -- Unfold ClonesState definitions and convert U.toLinearMap to U
  unfold ClonesState at hψ hφ
  simp only [LinearIsometry.coe_toLinearMap] at hψ hφ
  -- Left side: use the cloning property
  rw [hψ, hφ] at h
  -- Both sides expand using inner_tmul
  simp only [TensorProduct.inner_tmul] at h
  -- h now says: ⟨ψ|φ⟩ * ⟨ψ|φ⟩ = ⟨ψ|φ⟩ * ⟨e|e⟩
  exact h.symm

/-- If the blank state is normalized (⟨e|e⟩ = 1), then cloning two states implies
their inner product equals its own square: ⟨ψ|φ⟩ = ⟨ψ|φ⟩². -/
theorem cloning_inner_product_sq
    (U : H ⊗[𝕜] H →ₗᵢ[𝕜] H ⊗[𝕜] H) (e ψ φ : H)
    (he : @inner 𝕜 _ _ e e = (1 : 𝕜))
    (hψ : ClonesState U.toLinearMap e ψ) (hφ : ClonesState U.toLinearMap e φ) :
    (@inner 𝕜 _ _ ψ φ : 𝕜) = @inner 𝕜 _ _ ψ φ * @inner 𝕜 _ _ ψ φ := by
  have h := cloning_inner_product_constraint U e ψ φ hψ hφ
  simp only [he, mul_one] at h
  exact h

/-- The inner product constraint ⟨ψ|φ⟩ = ⟨ψ|φ⟩² implies ⟨ψ|φ⟩ * (1 - ⟨ψ|φ⟩) = 0. -/
theorem inner_sq_eq_self_imp (z : 𝕜) (h : z = z * z) : z * (1 - z) = 0 := by
  have : z * (1 - z) = z - z * z := by ring
  rw [this, ← h]
  ring

/-- **No-Cloning Theorem**: There is no inner-product-preserving linear map that can
clone two states whose inner product is neither 0 nor 1.

More precisely: if U is an isometry that clones both ψ and φ (with a normalized blank state),
then ⟨ψ|φ⟩ * (1 - ⟨ψ|φ⟩) = 0, which means ⟨ψ|φ⟩ = 0 (orthogonal) or ⟨ψ|φ⟩ = 1 (identical). -/
theorem no_cloning_theorem
    (U : H ⊗[𝕜] H →ₗᵢ[𝕜] H ⊗[𝕜] H) (e ψ φ : H)
    (he : @inner 𝕜 _ _ e e = (1 : 𝕜))
    (hψ : ClonesState U.toLinearMap e ψ) (hφ : ClonesState U.toLinearMap e φ) :
    @inner 𝕜 _ _ ψ φ * (1 - @inner 𝕜 _ _ ψ φ) = (0 : 𝕜) := by
  have h := cloning_inner_product_sq U e ψ φ he hψ hφ
  exact inner_sq_eq_self_imp (@inner 𝕜 _ _ ψ φ) h

/-!
## Application to qubits

We show that the no-cloning theorem prevents cloning of the |+⟩ state
when |0⟩ is already cloneable.
-/

/-- The |+⟩ state = (|0⟩ + |1⟩)/√2 -/
noncomputable def ketPlus : QubitSpace := (1/Real.sqrt 2 : ℂ) • (ket0 + ket1)

/-- The inner product ⟨0|+⟩ = 1/√2, which is neither 0 nor 1. -/
theorem inner_ket0_ketPlus : @inner ℂ _ _ ket0 ketPlus = (1/Real.sqrt 2 : ℂ) := by
  simp only [ketPlus, inner_smul_right]
  rw [inner_add_right, inner_ket0_ket0, inner_ket0_ket1]
  simp

/-- √2 > 1 -/
theorem sqrt_two_gt_one : (1 : ℝ) < Real.sqrt 2 := by
  have h : (1 : ℝ) = Real.sqrt 1 := by simp
  rw [h]
  apply Real.sqrt_lt_sqrt
  · norm_num
  · norm_num

/-- 1/√2 is strictly between 0 and 1. -/
theorem one_div_sqrt_two_pos : (0 : ℝ) < 1/Real.sqrt 2 := by
  apply div_pos one_pos
  exact Real.sqrt_pos.mpr (by norm_num : (2 : ℝ) > 0)

theorem one_div_sqrt_two_lt_one : (1/Real.sqrt 2 : ℝ) < 1 := by
  rw [div_lt_one (Real.sqrt_pos.mpr (by norm_num : (2 : ℝ) > 0))]
  exact sqrt_two_gt_one

/-- The product (1/√2)(1 - 1/√2) is nonzero because both factors are positive. -/
theorem one_div_sqrt_two_factor_ne_zero :
    (1/Real.sqrt 2 : ℝ) * (1 - 1/Real.sqrt 2) ≠ 0 := by
  apply mul_ne_zero
  · exact ne_of_gt one_div_sqrt_two_pos
  · have : 1 - 1/Real.sqrt 2 > 0 := sub_pos.mpr one_div_sqrt_two_lt_one
    exact ne_of_gt this

/-- Main application: The inner product ⟨0|+⟩ does not satisfy the cloning constraint.
Therefore, no isometry can clone both |0⟩ and |+⟩.

This is the concrete statement that quantum cloning is impossible for non-orthogonal states. -/
theorem no_cloning_ket0_ketPlus :
    ¬∃ (U : QubitSpace ⊗[ℂ] QubitSpace →ₗᵢ[ℂ] QubitSpace ⊗[ℂ] QubitSpace) (e : QubitSpace),
      @inner ℂ _ _ e e = (1 : ℂ) ∧
      ClonesState U.toLinearMap e ket0 ∧
      ClonesState U.toLinearMap e ketPlus := by
  intro ⟨U, e, he, h0, hplus⟩
  have hconstraint := no_cloning_theorem U e ket0 ketPlus he h0 hplus
  rw [inner_ket0_ketPlus] at hconstraint
  -- Now hconstraint says (1/√2) * (1 - 1/√2) = 0 in ℂ
  -- We show this contradicts the real result
  have hreal : (1/Real.sqrt 2 : ℝ) * (1 - 1/Real.sqrt 2) ≠ 0 := one_div_sqrt_two_factor_ne_zero
  -- Extract real equation from complex equation
  have hreal_zero : (1/Real.sqrt 2 : ℝ) * (1 - 1/Real.sqrt 2) = 0 := by
    have h : (((1/Real.sqrt 2 : ℝ) * (1 - 1/Real.sqrt 2) : ℝ) : ℂ) = (0 : ℂ) := by
      convert hconstraint using 1
      push_cast; ring
    exact Complex.ofReal_eq_zero.mp h
  exact hreal hreal_zero

end QuantumInformation

end QuantumMechanics
