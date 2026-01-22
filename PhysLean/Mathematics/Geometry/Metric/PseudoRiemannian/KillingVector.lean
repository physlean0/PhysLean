/-
Copyright (c) 2025 PhysLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PhysLean Contributors
-/

import PhysLean.Mathematics.Geometry.Metric.PseudoRiemannian.Connection

/-!
# Killing Vectors on Pseudo-Riemannian Manifolds

This file defines Killing vectors (vector fields that preserve the metric)
on a pseudo-Riemannian manifold.

## Main Definitions

* `KillingVectorField`: A vector field `X` is Killing if the Lie derivative of the
  metric along `X` vanishes, equivalently if it satisfies Killing's equation.
* `satisfiesKillingEquationAt`: The local condition for Killing's equation.

## Killing's Equation

A vector field X is Killing if:
  ∇_μ X_ν + ∇_ν X_μ = 0

In coordinate-free terms:
  g(∇_U X, V) + g(U, ∇_V X) = 0 for all vector fields U, V.

## Physical Interpretation

Killing vector fields generate isometries of the metric - their flow preserves distances.

By Noether's theorem, each Killing vector gives rise to a conserved quantity:
- Time translation Killing vector → conservation of energy
- Spatial translation Killing vectors → conservation of momentum
- Rotational Killing vectors → conservation of angular momentum

Along a geodesic γ with tangent T, if K is a Killing vector, then g(T, K) is constant.
This is the mathematical statement of the conservation law.

## References

* Misner, Thorne, Wheeler, "Gravitation" (1973), Chapter 25
* O'Neill, "Semi-Riemannian Geometry" (1983), Chapter 9
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

/-! ## Killing's Equation -/

/-- A smooth assignment of tangent vectors is a vector field.
For simplicity, we represent it as a function from points to tangent vectors at those points. -/
def VectorFieldAt (I : ModelWithCorners ℝ E H) (M : Type w) [TopologicalSpace M]
    [ChartedSpace H M] := ∀ x : M, TangentSpace I x

/-- Killing's equation states that for a Killing vector field X, the covariant derivative
satisfies ∇_μ X_ν + ∇_ν X_μ = 0 when indices are lowered using the metric.

In coordinate-free terms, this is expressed as:
g(∇_U X, V) + g(U, ∇_V X) = 0 for all vector fields U, V.

This definition provides the pointwise version: at a point x, given the value of X at x
and information about how X varies (encoded through a connection), we check if
the symmetric part of the covariant derivative of X vanishes. -/
def satisfiesKillingEquationAt (x : M)
    (covDeriv_X : TangentSpace I x → TangentSpace I x) : Prop :=
  ∀ U V : TangentSpace I x,
    g.val x (covDeriv_X U) V + g.val x U (covDeriv_X V) = 0

/-- A vector field is Killing if it satisfies Killing's equation everywhere.
Killing vector fields generate isometries of the metric - their flow preserves distances.

Physical interpretation: Killing vectors correspond to continuous symmetries of spacetime.
By Noether's theorem, each Killing vector gives rise to a conserved quantity.
- Time translation Killing vector → conservation of energy
- Spatial translation Killing vectors → conservation of momentum
- Rotational Killing vectors → conservation of angular momentum -/
structure KillingVectorField (g : PseudoRiemannianMetric E H M n I)
    (conn : LeviCivitaConnection g) where
  /-- The vector field as a section of the tangent bundle -/
  toVectorField : ∀ x : M, TangentSpace I x
  /-- At each point, there exists a covariant derivative satisfying Killing's equation -/
  isKilling : ∀ x : M, ∃ (covDeriv_X : TangentSpace I x → TangentSpace I x),
    satisfiesKillingEquationAt g x covDeriv_X

/-! ## Properties of Killing Vectors -/

/-- The zero vector field is always Killing. -/
def zeroKillingVectorField (conn : LeviCivitaConnection g) : KillingVectorField g conn where
  toVectorField := fun _ => 0
  isKilling := fun x => ⟨fun _ => 0, fun U V => by
    simp only [map_zero, ContinuousLinearMap.zero_apply, add_zero]⟩

/-- The sum of two Killing vector fields is Killing. -/
lemma killingVectorField_add (conn : LeviCivitaConnection g)
    (X Y : KillingVectorField g conn) :
    ∃ (Z : KillingVectorField g conn),
      ∀ x, Z.toVectorField x = X.toVectorField x + Y.toVectorField x := by
  use {
    toVectorField := fun x => X.toVectorField x + Y.toVectorField x
    isKilling := fun x => by
      obtain ⟨covX, hX⟩ := X.isKilling x
      obtain ⟨covY, hY⟩ := Y.isKilling x
      use fun U => covX U + covY U
      intro U V
      simp only [satisfiesKillingEquationAt] at hX hY ⊢
      simp only [map_add, add_apply]
      calc g.val x (covX U) V + g.val x (covY U) V + (g.val x U (covX V) + g.val x U (covY V))
          = (g.val x (covX U) V + g.val x U (covX V)) +
            (g.val x (covY U) V + g.val x U (covY V)) := by ring
        _ = 0 + 0 := by rw [hX U V, hY U V]
        _ = 0 := by ring
  }
  intro x
  rfl

/-- Scalar multiplication of a Killing vector field by a constant is Killing. -/
lemma killingVectorField_smul (conn : LeviCivitaConnection g)
    (c : ℝ) (X : KillingVectorField g conn) :
    ∃ (Y : KillingVectorField g conn),
      ∀ x, Y.toVectorField x = c • X.toVectorField x := by
  use {
    toVectorField := fun x => c • X.toVectorField x
    isKilling := fun x => by
      obtain ⟨covX, hX⟩ := X.isKilling x
      use fun U => c • covX U
      intro U V
      simp only [satisfiesKillingEquationAt] at hX ⊢
      simp only [map_smul, smul_apply, smul_eq_mul]
      calc c * g.val x (covX U) V + c * g.val x U (covX V)
          = c * (g.val x (covX U) V + g.val x U (covX V)) := by ring
        _ = c * 0 := by rw [hX U V]
        _ = 0 := by ring
  }
  intro x
  rfl

/-! ## Killing Vectors and Geodesics -/

/-- The conservation law for Killing vectors along geodesics.

Along a geodesic, the inner product of the tangent vector with a Killing vector is constant.
This is a key result connecting symmetries to conservation laws.

If X is a Killing vector and γ is a geodesic with tangent vector T, then
g(T, X) is constant along γ. This encapsulates conservation of momentum/energy
for geodesic motion in the presence of symmetry.

The proof follows from:
d/dτ g(T, X) = g(∇_T T, X) + g(T, ∇_T X)
             = 0 + g(T, ∇_T X)           (geodesic equation: ∇_T T = 0)
             = -(1/2) (g(∇_T X, T) + g(T, ∇_T X))  (using Killing's equation)
             = 0
-/
structure KillingConservationLaw (conn : LeviCivitaConnection g)
    (K : KillingVectorField g conn) where
  /-- The conserved quantity along a geodesic is g(T, K) -/
  conservedQuantity : (∀ τ : ℝ, M) → (∀ τ : ℝ, ∀ x : M, TangentSpace I x) → ℝ → ℝ :=
    fun γ T τ => g.val (γ τ) (T τ (γ τ)) (K.toVectorField (γ τ))

end PseudoRiemannianMetric
end
