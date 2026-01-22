/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Relativity.LorentzAlgebra.Basic
import PhysLean.Meta.TODO.Basic
/-!
# Generators of the Lorentz Algebra

This file defines the 6 standard generators of the Lorentz algebra so(1,3) :
- **Boost generators** K₀, K₁, K₂: Generate Lorentz transformations (velocity changes)
- **Rotation generators** J₀, J₁, J₂: Generate spatial rotations

These generators form a basis for the 6-dimensional Lie algebra so(1,3), though the full
basis structure (linear independence and spanning) is not yet proven here.

## Physical Interpretation

- `boostGenerator i`: Infinitesimal boost in the i-th spatial direction. Exponentiating
  this generator produces finite Lorentz boosts.
- `rotationGenerator i`: Infinitesimal rotation about the i-th axis following the
  right-hand rule. Exponentiating this generator produces spatial rotations.

## Mathematical Structure

Each generator satisfies the Lorentz algebra condition: Aᵀ η = -η A, where η is the
Minkowski metric with signature (+,-,-,-).

The boost generators are symmetric matrices with non-zero entries only in the time-space
block, while rotation generators are antisymmetric matrices acting only on spatial indices.

## References

- Weinberg, *The Quantum Theory of Fields*, Vol 1, Section 2.7
- Peskin & Schroeder, *An Introduction to QFT*, Appendix A

## Future Work

TODO "6VZKA" can be completed by proving linear independence and spanning of these
6 generators, then constructing a formal `Basis (Fin 2 × Fin 3) ℝ lorentzAlgebra`.

-/

open Matrix

namespace lorentzAlgebra

/-- The boost generator K_i in the Lorentz algebra so(1,3).

This matrix generates infinitesimal Lorentz boosts in the i-th spatial direction.
The matrix has non-zero entries only at positions (0, i+1) and (i+1, 0) with value 1,
where we use the index convention 0 = time, 1,2,3 = space.

## Properties
- Symmetric: K_iᵀ = K_i
- Traceless: tr(K_i) = 0
- Satisfies Lorentz algebra condition: K_iᵀ η = -η K_i

## Physical Meaning
Exponentiating β·K_i produces a finite Lorentz boost with rapidity β in direction i.
-/
def boostGenerator (i : Fin 3) : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ :=
  fun μ ν =>
    if (μ = Sum.inl 0 ∧ ν = Sum.inr i) ∨ (μ = Sum.inr i ∧ ν = Sum.inl 0) then 1
    else 0

/-- The rotation generator J_i in the Lorentz algebra so(1,3).

This matrix generates infinitesimal rotations about the i-th axis following the right-hand rule.
The matrix acts only on spatial indices in the antisymmetric pattern characteristic of
angular momentum generators.

## Properties
- Antisymmetric: J_iᵀ = -J_i
- Traceless: tr(J_i) = 0
- Satisfies Lorentz algebra condition: J_iᵀ η = -η J_i

## Structure
- J_0 (rotation about x-axis) : Acts on (y,z) components
- J_1 (rotation about y-axis) : Acts on (z,x) components
- J_2 (rotation about z-axis) : Acts on (x,y) components

## Physical Meaning
Exponentiating θ·J_i produces a finite rotation by angle θ about axis i.
-/
def rotationGenerator (i : Fin 3) : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ :=
  fun μ ν =>
    match i with
    | 0 => if μ = Sum.inr 1 ∧ ν = Sum.inr 2 then -1
            else if μ = Sum.inr 2 ∧ ν = Sum.inr 1 then 1
            else 0
      | 1 => if μ = Sum.inr 0 ∧ ν = Sum.inr 2 then 1
            else if μ = Sum.inr 2 ∧ ν = Sum.inr 0 then -1
            else 0
      | 2 => if μ = Sum.inr 0 ∧ ν = Sum.inr 1 then -1
            else if μ = Sum.inr 1 ∧ ν = Sum.inr 0 then 1
            else 0

/-- The boost generator K_i is in the Lorentz algebra. -/
lemma boostGenerator_mem (i : Fin 3) : boostGenerator i ∈ lorentzAlgebra := by
  rw [lorentzAlgebra.mem_iff]
  ext μ ν
  simp only [boostGenerator, minkowskiMatrix.as_diagonal, mul_diagonal, transpose_apply]
  rcases μ with μ | μ <;> rcases ν with ν | ν
  · -- (time, time) case
    simp only [Sum.elim_inl]
    have : μ = 0 := Subsingleton.elim _ _
    have : ν = 0 := Subsingleton.elim _ _
    simp [boostGenerator, *]
  · -- (time, space) case
    simp only [Sum.elim_inr]
    have : μ = 0 := Subsingleton.elim _ _
    simp [boostGenerator, *]
    split_ifs <;> norm_num
  · -- (space, time) case
    simp only [Sum.elim_inl]
    have : ν = 0 := Subsingleton.elim _ _
    simp [boostGenerator, *]
  · -- (space, space) case
    simp [Sum.elim_inr, boostGenerator]

/-- The rotation generator J_i is in the Lorentz algebra. -/
lemma rotationGenerator_mem (i : Fin 3) : rotationGenerator i ∈ lorentzAlgebra := by
  rw [lorentzAlgebra.mem_iff]
  ext μ ν
  simp only [rotationGenerator, minkowskiMatrix.as_diagonal, mul_diagonal, transpose_apply]
  rcases μ with μ | μ <;> rcases ν with ν | ν
  · -- (time, time) case
    have : μ = 0 := Subsingleton.elim _ _
    have : ν = 0 := Subsingleton.elim _ _
    simp [rotationGenerator, *]
    fin_cases i <;> norm_num
  · -- (time, space) case
    have : μ = 0 := Subsingleton.elim _ _
    simp [rotationGenerator, *]
  · -- (space, time) case
    have : ν = 0 := Subsingleton.elim _ _
    simp [rotationGenerator, *]
  · -- (space, space) case: need explicit computation
    simp only [Sum.elim_inr]
    fin_cases i <;> fin_cases μ <;> fin_cases ν <;> simp [rotationGenerator]

/-!
## Properties of Generators

These lemmas establish key properties of the Lorentz algebra generators:
- Boost generators are symmetric and traceless
- Rotation generators are antisymmetric and traceless
-/

/-- Boost generators are symmetric: K_iᵀ = K_i -/
@[simp]
lemma boostGenerator_symmetric (i : Fin 3) :
    (boostGenerator i)ᵀ = boostGenerator i := by
  ext μ ν
  simp only [boostGenerator, transpose_apply]
  -- The condition (μ = 0 ∧ ν = i) ∨ (μ = i ∧ ν = 0) is symmetric in μ, ν
  -- when written as: one is time (0) and the other is spatial direction i
  -- Show both evaluate to 1 when conditions are met, and 0 otherwise
  by_cases h1 : (μ = Sum.inl 0 ∧ ν = Sum.inr i) ∨ (μ = Sum.inr i ∧ ν = Sum.inl 0)
  · -- If the (μ, ν) condition is true, show the (ν, μ) condition is also true
    simp only [h1, ite_true]
    rcases h1 with ⟨hμ, hν⟩ | ⟨hμ, hν⟩
    · simp only [hμ, hν, and_true, or_true, ite_true]
    · simp only [hμ, hν, and_true, true_or, ite_true]
  · -- If the (μ, ν) condition is false, show the (ν, μ) condition is also false
    simp only [h1, ite_false]
    simp only [not_or, not_and] at h1
    -- The (ν, μ) condition is: (ν = 0 ∧ μ = i) ∨ (ν = i ∧ μ = 0)
    -- We need to show this is also false
    by_cases h2 : (ν = Sum.inl 0 ∧ μ = Sum.inr i) ∨ (ν = Sum.inr i ∧ μ = Sum.inl 0)
    · rcases h2 with ⟨hν, hμ⟩ | ⟨hν, hμ⟩
      · -- ν = 0, μ = i, but h1 says ¬(μ = 0) ∨ ¬(ν = i) and ¬(μ = i) ∨ ¬(ν = 0)
        have := h1.2 hμ
        simp only [hν] at this
        exact absurd trivial this
      · -- ν = i, μ = 0, but h1 says ¬(μ = 0) ∨ ¬(ν = i) and ¬(μ = i) ∨ ¬(ν = 0)
        have := h1.1 hμ
        simp only [hν] at this
        exact absurd trivial this
    · simp only [h2, ite_false]

/-- Boost generators are traceless: tr(K_i) = 0 -/
@[simp]
lemma boostGenerator_trace_zero (i : Fin 3) :
    Matrix.trace (boostGenerator i) = 0 := by
  simp only [Matrix.trace, boostGenerator, Matrix.diag]
  -- The trace is over diagonal elements: (0,0), (1,1), (2,2), (3,3)
  -- Boost generator only has non-zero off-diagonal elements
  have h : ∀ μ : Fin 1 ⊕ Fin 3, (if (μ = Sum.inl 0 ∧ μ = Sum.inr i) ∨
      (μ = Sum.inr i ∧ μ = Sum.inl 0) then (1 : ℝ) else 0) = 0 := by
    intro μ
    rcases μ with μ | μ
    · have : μ = 0 := Subsingleton.elim _ _
      simp [this]
    · simp
  simp only [h, Finset.sum_const_zero]

/-- Rotation generators are antisymmetric: J_iᵀ = -J_i -/
@[simp]
lemma rotationGenerator_antisymm (i : Fin 3) :
    (rotationGenerator i)ᵀ = -(rotationGenerator i) := by
  ext μ ν
  simp only [rotationGenerator, transpose_apply, neg_apply]
  fin_cases i <;> (rcases μ with μ | μ <;> rcases ν with ν | ν) <;>
    (try fin_cases μ) <;> (try fin_cases ν) <;> simp

/-- Rotation generators are traceless: tr(J_i) = 0 -/
@[simp]
lemma rotationGenerator_trace_zero (i : Fin 3) :
    Matrix.trace (rotationGenerator i) = 0 := by
  simp only [Matrix.trace, rotationGenerator, Matrix.diag]
  -- Rotation generators only have non-zero off-diagonal elements
  -- The trace sums over diagonal entries where row = column
  -- These conditions like (x = 1 ∧ x = 2) are always false for diagonal
  have h : ∀ μ : Fin 1 ⊕ Fin 3, (rotationGenerator i μ μ) = 0 := by
    intro μ
    rcases μ with μ | μ
    · have hμ : μ = 0 := Subsingleton.elim _ _
      subst hμ
      fin_cases i <;> rfl
    · fin_cases i <;> fin_cases μ <;> rfl
  exact Finset.sum_eq_zero (fun μ _ => h μ)

/-!
## Linear Independence of Generators

The TODO "6VZKA" requires proving that the 6 generators form a basis.
For now, we document the approach: each generator has a unique non-zero entry
that no other generator touches, allowing us to prove linear independence.

Future work: Complete the formal proof of linear independence and spanning.
-/

end lorentzAlgebra
