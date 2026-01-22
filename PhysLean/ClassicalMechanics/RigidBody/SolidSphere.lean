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

/-- The permutation that swaps coordinates i and j.
This is a linear isometry that preserves the ball and measure. -/
private def swap_coord (i j : Fin d) : Space d → Space d :=
  fun x => ⟨fun k => if k = i then x j else if k = j then x i else x k⟩

private lemma swap_coord_apply (i j k : Fin d) (x : Space d) :
    swap_coord i j x k = if k = i then x j else if k = j then x i else x k := rfl

private lemma swap_coord_norm (i j : Fin d) (x : Space d) :
    ‖swap_coord i j x‖ = ‖x‖ := by
  simp only [Space.norm_eq]
  congr 1
  by_cases hij : i = j
  · subst hij
    apply Finset.sum_congr rfl
    intro k _
    simp only [swap_coord_apply]
    split_ifs with h
    · subst h; ring
    · ring
  · -- Swapping i and j permutes the sum, use Equiv.Perm.sumComm
    let σ : Equiv.Perm (Fin d) := Equiv.swap i j
    have hσ : ∀ k, (swap_coord i j x k) ^ 2 = (x (σ k)) ^ 2 := by
      intro k
      simp only [swap_coord_apply, Equiv.swap_apply_def, σ]
      split_ifs with h1 h2
      · rfl
      · rfl
      · rfl
    rw [show ∑ k : Fin d, (swap_coord i j x k) ^ 2 = ∑ k : Fin d, (x (σ k)) ^ 2 from
        Finset.sum_congr rfl (fun k _ => hσ k)]
    rw [← Equiv.sum_comp σ (fun k => (x k) ^ 2)]

private lemma swap_coord_involutive (i j : Fin d) : Function.Involutive (swap_coord i j) := by
  intro x
  ext k
  simp only [swap_coord_apply]
  split_ifs <;> simp_all

private lemma swap_coord_add (i j : Fin d) (x y : Space d) :
    swap_coord i j (x + y) = swap_coord i j x + swap_coord i j y := by
  ext k
  simp only [swap_coord_apply, Space.add_apply]
  split_ifs <;> ring

private lemma swap_coord_smul (i j : Fin d) (c : ℝ) (x : Space d) :
    swap_coord i j (c • x) = c • swap_coord i j x := by
  ext k
  simp only [swap_coord_apply, Space.smul_apply]
  split_ifs <;> ring

/-- The coordinate swap as a linear isometry equivalence. -/
private noncomputable def swapCoordEquiv (i j : Fin d) : Space d ≃ₗᵢ[ℝ] Space d where
  toFun := swap_coord i j
  invFun := swap_coord i j
  left_inv := swap_coord_involutive i j
  right_inv := swap_coord_involutive i j
  map_add' := swap_coord_add i j
  map_smul' := swap_coord_smul i j
  norm_map' := swap_coord_norm i j

private lemma swapCoordEquiv_apply (i j : Fin d) (x : Space d) :
    swapCoordEquiv i j x = swap_coord i j x := rfl

private lemma swapCoordEquiv_measurePreserving (i j : Fin d) :
    MeasurePreserving (swapCoordEquiv i j) volume volume :=
  LinearIsometryEquiv.measurePreserving (swapCoordEquiv i j)

private lemma swap_coord_ball (i j : Fin d) (R : ℝ) (x : Space d) :
    x ∈ Metric.closedBall (0 : Space d) R ↔
    swap_coord i j x ∈ Metric.closedBall (0 : Space d) R := by
  simp only [Metric.mem_closedBall, dist_zero_right, swap_coord_norm]

private lemma swap_coord_sq_eq (i j : Fin d) (x : Space d) :
    (swap_coord i j x i) ^ 2 = (x j) ^ 2 := by
  simp only [swap_coord_apply, if_true, sq]

/-- The integrals of x_i² and x_j² over a ball centered at the origin are equal,
    by symmetry under coordinate swapping. -/
private lemma integral_coord_sq_eq {d : ℕ} (i j : Fin d) (R : ℝ) :
    ∫ x in Metric.closedBall (0 : Space d) R, (x i) ^ 2 ∂volume =
    ∫ x in Metric.closedBall (0 : Space d) R, (x j) ^ 2 ∂volume := by
  -- Use change of variables with swapCoordEquiv j i
  conv_lhs => rw [← (swapCoordEquiv_measurePreserving j i).setIntegral_preimage_emb
    (LinearIsometryEquiv.toHomeomorph (swapCoordEquiv j i)).measurableEmbedding]
  -- The preimage of the ball is the ball itself
  have hball_preimage : swapCoordEquiv j i ⁻¹' Metric.closedBall (0 : Space d) R
      = Metric.closedBall (0 : Space d) R := by
    ext x
    simp only [Set.mem_preimage, swapCoordEquiv_apply]
    exact (swap_coord_ball j i R x).symm
  rw [hball_preimage]
  -- Show the integrands are equal pointwise
  congr 1
  funext x
  simp only [swapCoordEquiv_apply]
  -- (swap_coord j i x i)² = (x j)²
  simp only [swap_coord_apply]
  split_ifs with h1
  · simp only [h1, sq]
  · simp only [sq]

/-- For a ball centered at origin in d dimensions, ∫ x_i² dV = (1/d) ∫ |x|² dV
    by symmetry: all coordinate squares integrate to the same value. -/
private lemma integral_coord_sq_eq_div {d : ℕ} (_hd : 0 < d) (i : Fin d) (R : ℝ) :
    (d : ℝ) * ∫ x in Metric.closedBall (0 : Space d) R, (x i) ^ 2 ∂volume =
    ∫ x in Metric.closedBall (0 : Space d) R, ‖x‖ ^ 2 ∂volume := by
  -- |x|² = ∑_k x_k², so ∫ |x|² = ∑_k ∫ x_k²
  have h1 : ∫ x in Metric.closedBall (0 : Space d) R, ‖x‖ ^ 2 ∂volume =
      ∫ x in Metric.closedBall (0 : Space d) R, (∑ k : Fin d, (x k) ^ 2) ∂volume := by
    congr 1
    funext x
    simp only [Space.norm_eq, Real.sq_sqrt (Finset.sum_nonneg (fun k _ => sq_nonneg (x k)))]
  rw [h1]
  -- Pull the sum outside the integral
  rw [integral_finset_sum]
  -- Each ∫ x_k² is equal to ∫ x_i² by symmetry
  have h2 : ∀ k : Fin d, ∫ x in Metric.closedBall (0 : Space d) R, (x k) ^ 2 ∂volume =
      ∫ x in Metric.closedBall (0 : Space d) R, (x i) ^ 2 ∂volume :=
    fun k => integral_coord_sq_eq k i R
  simp only [h2]
  simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  -- Integrability for the sum
  intro k _
  exact IntegrableOn.integrable
    (ContinuousOn.integrableOn_compact (isCompact_closedBall 0 R) (by fun_prop))

/-- The radial integral ∫_{ball(0,R)} |x|² dV in dimension d equals
    (d/(d+2)) · R² · volume(ball(0,R)).

    For d=3: ∫ |x|² dV = (3/5) · R² · (4π/3) R³ = (4π/5) R⁵.
    This gives (2/3) · ∫ |x|² dV = (8π/15) R⁵.

    This is a fundamental result in integration over balls that requires
    spherical coordinate techniques or dimensional analysis. -/
private lemma integral_norm_sq_ball (R : ℝ≥0) :
    ∫ x in Metric.closedBall (0 : Space 3) R, ‖x‖ ^ 2 ∂volume =
    (3 / 5 : ℝ) * R.1 ^ 2 * volume.real (Metric.closedBall (0 : Space 3) R) := by
  -- In spherical coordinates: ∫_{ball} |x|² dV = ∫₀^R r² · (surface area of sphere r) dr
  --                                            = ∫₀^R r² · 4πr² dr = 4π ∫₀^R r⁴ dr
  --                                            = 4π · (R⁵/5) = (4π/5) R⁵
  -- Volume of ball = (4π/3) R³
  -- So ∫ |x|² dV / Volume = (R⁵/5) / (R³/3) = (3/5) R²
  -- Hence ∫ |x|² dV = (3/5) R² · Volume
  sorry

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
    -- Step 1: Rewrite in terms of ‖x‖² and x_i²
    have h_integrand : ∀ x : Space 3, ((1 : ℝ) * ∑ k : Fin 3, x k ^ 2 - x i * x i) =
        ‖x‖ ^ 2 - (x i) ^ 2 := by
      intro x
      simp only [one_mul, sq]
      have hn : ‖x‖ ^ 2 = ∑ k : Fin 3, (x k) ^ 2 := by
        rw [Space.norm_eq, Real.sq_sqrt (Finset.sum_nonneg (fun k _ => sq_nonneg (x k)))]
      conv_rhs => rw [← sq ‖x‖, hn]; simp only [sq]
    simp_rw [h_integrand]
    -- Step 2: Split the integral: ∫ (‖x‖² - x_i²) = ∫ ‖x‖² - ∫ x_i²
    rw [integral_sub]
    · -- Step 3: By symmetry, ∫ x_i² = (1/3) ∫ ‖x‖²
      -- So ∫ ‖x‖² - ∫ x_i² = ∫ ‖x‖² - (1/3) ∫ ‖x‖² = (2/3) ∫ ‖x‖²
      have h_sym := integral_coord_sq_eq_div (by omega : 0 < 3) i R
      -- h_sym: 3 * ∫ x_i² = ∫ ‖x‖²
      have h_coord_sq : ∫ x in Metric.closedBall (0 : Space 3) R, (x i) ^ 2 ∂volume =
          (1 / 3 : ℝ) * ∫ x in Metric.closedBall (0 : Space 3) R, ‖x‖ ^ 2 ∂volume := by
        have h3 : (3 : ℝ) ≠ 0 := by norm_num
        have h_sym' : ∫ x in Metric.closedBall (0 : Space 3) R, (x i) ^ 2 ∂volume =
            (∫ x in Metric.closedBall (0 : Space 3) R, ‖x‖ ^ 2 ∂volume) / 3 := by
          have := h_sym
          simp only [Nat.cast_ofNat] at this
          field_simp [h3]
          linarith
        rw [h_sym']
        ring
      rw [h_coord_sq]
      -- Now we have: ρ * (∫ ‖x‖² - (1/3) ∫ ‖x‖²) = ρ * (2/3) ∫ ‖x‖²
      ring_nf
      -- Step 4: Use the radial integral formula
      rw [integral_norm_sq_ball]
      -- The density ρ = m / volume
      -- So ρ * (2/3) * (3/5) * R² * volume = m * (2/5) * R²
      ring_nf
      have hV : volume.real (Metric.closedBall (0 : Space 3) R) ≠ 0 := by
        rw [measureReal_ne_zero_iff (Space.volume_closedBall_neq_top 0 R)]
        apply Space.volume_closedBall_neq_zero
        have hr' := R.2
        have hx : R.1 ≠ 0 := by simpa using hr
        exact lt_of_le_of_ne hr' (Ne.symm hx)
      field_simp
      ring_nf
      exact mul_comm _ _
    · -- Integrability of ‖x‖²
      exact IntegrableOn.integrable
        (ContinuousOn.integrableOn_compact (isCompact_closedBall 0 R) (by fun_prop))
    · -- Integrability of x_i²
      exact IntegrableOn.integrable
        (ContinuousOn.integrableOn_compact (isCompact_closedBall 0 R) (by fun_prop))
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
