/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.ClassicalMechanics.RigidBody.Basic
/-!

# The solid sphere as a rigid body

In this module we consider the solid sphere as a rigid body, and compute its mass,
center of mass and inertia tensor.

-/

open Manifold
open MeasureTheory
namespace RigidBody
open NNReal

/-- The solid sphere as a rigid body. -/
noncomputable def solidSphere (d : ℕ) (m R : ℝ≥0) : RigidBody d where
  ρ := ⟨⟨fun f => m / volume.real (Metric.closedBall (0 : Space d) R) *
      ∫ x in Metric.closedBall (0 : Space d) R, f x ∂volume,
    by
    intro f g
    simp only [ContMDiffMap.coe_add, Pi.add_apply]
    rw [integral_add]
    ring
    · exact IntegrableOn.integrable
        (ContinuousOn.integrableOn_compact (isCompact_closedBall 0 R) (by fun_prop))
    · exact IntegrableOn.integrable
        (ContinuousOn.integrableOn_compact (isCompact_closedBall 0 R) (by fun_prop))⟩, by
      intro r f
      simp only [ContMDiffMap.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
      rw [integral_const_mul]
      ring⟩

lemma solidSphere_mass {d : ℕ} (m R : ℝ≥0) (hr : R ≠ 0) : (solidSphere d.succ m R).mass = m := by
  simp only [mass, solidSphere]
  simp only [Nat.succ_eq_add_one, LinearMap.coe_mk, AddHom.coe_mk, ContMDiffMap.coeFn_mk,
    integral_const, MeasurableSet.univ, measureReal_restrict_apply, Set.univ_inter, smul_eq_mul,
    mul_one]
  have h1 : (@volume (Space d.succ) measureSpaceOfInnerProductSpace).real
      (Metric.closedBall 0 R) ≠ 0 := by
    refine (measureReal_ne_zero_iff ?_).mpr ?_
    · apply Space.volume_closedBall_neq_top
    · apply Space.volume_closedBall_neq_zero
      have hr' := R.2
      have hx : R.1 ≠ 0 := by simpa using hr
      apply lt_of_le_of_ne hr' (Ne.symm hx)
  field_simp

/-- The center of mass of a solid sphere located at the origin is `0`. -/
lemma solidSphere_centerOfMass {d : ℕ} (m R : ℝ≥0) : (solidSphere d.succ m R).centerOfMass = 0 := by
  ext i
  simp only [Nat.succ_eq_add_one, centerOfMass, solidSphere, one_div, LinearMap.coe_mk,
    AddHom.coe_mk, ContMDiffMap.coeFn_mk, smul_eq_mul, Space.zero_apply, mul_eq_zero, inv_eq_zero,
    div_eq_zero_iff, coe_eq_zero]
  right
  right
  suffices ∫ x in Metric.closedBall (0 : Space d.succ) R, x i ∂MeasureSpace.volume
    = -∫ x in Metric.closedBall (0 : Space d.succ) R, x i ∂MeasureSpace.volume by linarith
  rw [← integral_neg]
  simp only [← integral_indicator measurableSet_closedBall, Set.indicator, Metric.mem_closedBall,
    dist_zero_right]
  rw [← integral_neg_eq_self]
  norm_num

/-- The reflection that negates the k-th coordinate.
This is a linear isometry that preserves the ball and measure.
For i ≠ j, the function x_i * x_j is odd under flip_coord i (or flip_coord j). -/
private def flip_coord (k : Fin d) : Space d → Space d :=
  fun x => ⟨fun i => if i = k then -x i else x i⟩

private lemma flip_coord_apply (k i : Fin d) (x : Space d) :
    flip_coord k x i = if i = k then -x i else x i := rfl

private lemma flip_coord_norm (k : Fin d) (x : Space d) :
    ‖flip_coord k x‖ = ‖x‖ := by
  simp only [Space.norm_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [flip_coord_apply]
  split_ifs with h <;> ring

private lemma flip_coord_involutive (k : Fin d) : Function.Involutive (flip_coord k) := by
  intro x
  ext i
  simp only [flip_coord_apply]
  split_ifs <;> ring

private lemma flip_coord_prod_neg (i j : Fin d) (hij : i ≠ j) (x : Space d) :
    flip_coord i x i * flip_coord i x j = -(x i * x j) := by
  simp only [flip_coord_apply]
  simp only [if_true, if_neg (Ne.symm hij)]
  ring

private lemma flip_coord_add (k : Fin d) (x y : Space d) :
    flip_coord k (x + y) = flip_coord k x + flip_coord k y := by
  ext i
  simp only [flip_coord_apply, Space.add_apply]
  split_ifs <;> ring

private lemma flip_coord_smul (k : Fin d) (c : ℝ) (x : Space d) :
    flip_coord k (c • x) = c • flip_coord k x := by
  ext i
  simp only [flip_coord_apply, Space.smul_apply]
  split_ifs <;> ring

/-- The coordinate reflection as a linear isometry equivalence. -/
private noncomputable def flipCoordEquiv (k : Fin d) : Space d ≃ₗᵢ[ℝ] Space d where
  toFun := flip_coord k
  invFun := flip_coord k
  left_inv := flip_coord_involutive k
  right_inv := flip_coord_involutive k
  map_add' := flip_coord_add k
  map_smul' := flip_coord_smul k
  norm_map' := flip_coord_norm k

private lemma flipCoordEquiv_apply (k : Fin d) (x : Space d) :
    flipCoordEquiv k x = flip_coord k x := rfl

private lemma flipCoordEquiv_measurePreserving (k : Fin d) :
    MeasurePreserving (flipCoordEquiv k) volume volume :=
  LinearIsometryEquiv.measurePreserving (flipCoordEquiv k)

private lemma flip_coord_ball (k : Fin d) (R : ℝ) (x : Space d) :
    x ∈ Metric.closedBall (0 : Space d) R ↔
    flip_coord k x ∈ Metric.closedBall (0 : Space d) R := by
  simp only [Metric.mem_closedBall, dist_zero_right, flip_coord_norm]

/-- The moment of inertia tensor of a solid sphere through its center of mass is
  `2/5 m R^2 * I`.

  This is the fundamental result for a uniform solid sphere: due to spherical symmetry,
  the inertia tensor is isotropic (proportional to the identity matrix). The coefficient
  2/5 comes from the integral ∫_ball (|x|² - x_i²) dV = (2/3) ∫_ball |x|² dV = (2/5) mR².

  Off-diagonal entries vanish because x_i * x_j (i ≠ j) is odd under partial reflection
  (negating only coordinate i), and the ball and measure are invariant under this reflection.-/
lemma solidSphere_inertiaTensor (m R : ℝ≥0) (hr : R ≠ 0) :
    (solidSphere 3 m R).inertiaTensor = (2/5 * m.1 * R.1^2) • (1 : Matrix _ _ _) := by
  ext i j
  simp only [inertiaTensor, solidSphere, LinearMap.coe_mk, AddHom.coe_mk,
    ContMDiffMap.coeFn_mk, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  by_cases hij : i = j
  · -- Diagonal case: I_{ii} = (2/5) m R² (requires integral computation)
    subst hij
    simp only [↓reduceIte, mul_one]
    -- The diagonal entries require computing ∫ (|x|² - x_i²) dV over the ball.
    -- The key steps are:
    -- 1. By spherical symmetry: ∫ x_i² dV = (1/d) ∫ |x|² dV for each i (here d=3)
    -- 2. So ∫ (|x|² - x_i²) dV = ((d-1)/d) ∫ |x|² dV = (2/3) ∫ |x|² dV
    -- 3. In spherical coordinates: ∫_{ball} |x|² dV = ∫₀^R r² · 4πr² dr = (4π/5) R⁵
    -- 4. Volume of ball: V = (4π/3) R³, so ρ = m/V = 3m/(4πR³)
    -- 5. Combined: ρ · (2/3) · (4π/5) R⁵ = (3m/(4πR³)) · (8π/15) R⁵ = (2/5) m R²
    -- This computation requires spherical coordinate integrals not yet available.
    sorry
  · -- Off-diagonal case: I_{ij} = 0 for i ≠ j (by partial reflection symmetry)
    simp only [hij, ↓reduceIte, mul_zero]
    -- The integrand is 0 * (∑ k, x_k²) - x_i * x_j = 0 - x_i * x_j = -x_i * x_j
    -- We need to show: ρ * ∫ (-x_i * x_j) = 0, which holds if ∫ (x_i * x_j) = 0
    -- First simplify 0 * ∑ k, ... to 0
    simp only [zero_mul, zero_sub]
    -- Now we need: ρ * ∫ (-(x_i * x_j)) = 0
    rw [integral_neg]
    -- Now we need: ρ * (-∫ (x_i * x_j)) = 0
    suffices h : ∫ x in Metric.closedBall (0 : Space 3) R, (x i * x j) ∂volume = 0 by
      rw [h, neg_zero, mul_zero]
    -- The integral vanishes because x_i * x_j is odd under partial reflection (flip_coord i).
    -- We show ∫ f = -∫ f by change of variables with flipCoordEquiv i.
    suffices heq : ∫ x in Metric.closedBall (0 : Space 3) R, (x i * x j) ∂volume
        = -∫ x in Metric.closedBall (0 : Space 3) R, (x i * x j) ∂volume by linarith
    rw [← integral_neg]
    -- Use measure preservation: ∫ f = ∫ (f ∘ flipCoordEquiv i) by change of variables
    conv_lhs => rw [← (flipCoordEquiv_measurePreserving i).setIntegral_preimage_emb
      (LinearIsometryEquiv.toHomeomorph (flipCoordEquiv i)).measurableEmbedding]
    -- The preimage of the ball under flipCoordEquiv i is the ball itself
    have hball_preimage : flipCoordEquiv i ⁻¹' Metric.closedBall (0 : Space 3) R
        = Metric.closedBall (0 : Space 3) R := by
      ext x
      simp only [Set.mem_preimage, flipCoordEquiv_apply]
      exact (flip_coord_ball i R x).symm
    rw [hball_preimage]
    -- Now show the integrands are equal pointwise
    congr 1
    funext x
    simp only [flipCoordEquiv_apply]
    exact flip_coord_prod_neg i j hij x

end RigidBody
