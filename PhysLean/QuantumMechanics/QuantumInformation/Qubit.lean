/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.QuantumMechanics.FiniteTarget.HilbertSpace
import Mathlib.Analysis.InnerProductSpace.PiL2
/-!

# Qubit - The fundamental unit of quantum information

A qubit is a two-level quantum system, represented by a 2-dimensional complex Hilbert space.

This file contains:
- Definition of the qubit Hilbert space
- The computational basis states |0⟩ and |1⟩
- Proof that the computational basis is orthonormal
- Basic properties of qubit states

-/

namespace QuantumMechanics

namespace QuantumInformation

/-- The Hilbert space of a single qubit is a 2-dimensional complex vector space. -/
abbrev QubitSpace : Type := FiniteHilbertSpace 2

/-- The |0⟩ computational basis state. -/
noncomputable def ket0 : QubitSpace := EuclideanSpace.single 0 1

/-- The |1⟩ computational basis state. -/
noncomputable def ket1 : QubitSpace := EuclideanSpace.single 1 1

/-!

## Orthonormality of the computational basis

The computational basis is orthonormal, which follows from `EuclideanSpace.orthonormal_single`.

-/

/-- The computational basis is orthonormal. -/
theorem orthonormal_computational_basis :
    Orthonormal ℂ (fun i : Fin 2 => EuclideanSpace.single i (1 : ℂ)) :=
  EuclideanSpace.orthonormal_single

/-- The |0⟩ state has unit norm. -/
@[simp]
theorem ket0_norm : ‖ket0‖ = 1 := by
  rw [ket0, EuclideanSpace.norm_single]
  exact norm_one

/-- The |1⟩ state has unit norm. -/
@[simp]
theorem ket1_norm : ‖ket1‖ = 1 := by
  rw [ket1, EuclideanSpace.norm_single]
  exact norm_one

/-- The inner product ⟨0|0⟩ = 1. -/
theorem inner_ket0_ket0 : @inner ℂ _ _ ket0 ket0 = 1 := by
  have h := orthonormal_computational_basis
  rw [orthonormal_iff_ite] at h
  exact h 0 0

/-- The inner product ⟨1|1⟩ = 1. -/
theorem inner_ket1_ket1 : @inner ℂ _ _ ket1 ket1 = 1 := by
  have h := orthonormal_computational_basis
  rw [orthonormal_iff_ite] at h
  exact h 1 1

/-- The inner product ⟨0|1⟩ = 0 (orthogonality). -/
theorem inner_ket0_ket1 : @inner ℂ _ _ ket0 ket1 = 0 := by
  have h := orthonormal_computational_basis
  rw [orthonormal_iff_ite] at h
  have h' := h 0 1
  simp at h'
  rw [ket0, ket1]
  exact h'

/-- The inner product ⟨1|0⟩ = 0 (orthogonality). -/
theorem inner_ket1_ket0 : @inner ℂ _ _ ket1 ket0 = 0 := by
  have h := orthonormal_computational_basis
  rw [orthonormal_iff_ite] at h
  have h' := h 1 0
  simp at h'
  rw [ket0, ket1]
  exact h'

/-- The computational basis states are distinct. -/
theorem ket0_ne_ket1 : ket0 ≠ ket1 := by
  intro h
  have h1 : @inner ℂ _ _ ket0 ket0 = @inner ℂ _ _ ket0 ket1 := by rw [h]
  rw [inner_ket0_ket0, inner_ket0_ket1] at h1
  norm_num at h1

/-!

## Qubit state normalization

A general qubit state |ψ⟩ = α|0⟩ + β|1⟩ is normalized iff |α|² + |β|² = 1.

-/

/-- A qubit state parameterized by amplitudes α and β. -/
noncomputable def qubitState (α β : ℂ) : QubitSpace := α • ket0 + β • ket1

/-- The norm squared of a qubit state equals |α|² + |β|². -/
theorem qubitState_norm_sq (α β : ℂ) :
    ‖qubitState α β‖^2 = Complex.normSq α + Complex.normSq β := by
  simp only [qubitState, ket0, ket1]
  have hinner : @inner ℂ _ _ (α • EuclideanSpace.single (0 : Fin 2) (1 : ℂ))
      (β • EuclideanSpace.single (1 : Fin 2) (1 : ℂ)) = 0 := by
    rw [inner_smul_left, inner_smul_right]
    have h := orthonormal_computational_basis
    rw [orthonormal_iff_ite] at h
    have h01 := h 0 1
    simp at h01
    rw [h01]
    simp
  have hpyth := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hinner
  rw [sq]
  convert hpyth using 1
  simp only [norm_smul, EuclideanSpace.norm_single, norm_one, mul_one]
  rw [← sq, ← sq, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]

/-- A normalized qubit state has |α|² + |β|² = 1. -/
theorem qubitState_normalized_iff (α β : ℂ) :
    ‖qubitState α β‖ = 1 ↔ Complex.normSq α + Complex.normSq β = 1 := by
  rw [← qubitState_norm_sq]
  constructor
  · intro h
    rw [h]
    norm_num
  · intro h
    have pos : 0 ≤ ‖qubitState α β‖ := norm_nonneg _
    nlinarith [sq_nonneg ‖qubitState α β‖]

end QuantumInformation

end QuantumMechanics
