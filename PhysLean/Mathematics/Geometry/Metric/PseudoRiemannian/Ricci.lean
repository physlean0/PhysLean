/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Mathematics.Geometry.Metric.PseudoRiemannian.Curvature
/-!
# Ricci Tensor and Scalar Curvature

This file defines the Ricci tensor and scalar curvature, which are contractions of the
Riemann curvature tensor. These are the curvature quantities that appear directly in
Einstein's field equations.

## Main definitions

* `RicciTensorAt`: The Ricci tensor Rᵢⱼ at a point
* `RicciTensor`: The Ricci tensor as a field
* `scalarCurvature`: The scalar curvature R = gⁱʲRᵢⱼ

## Physics context

The Ricci tensor Rᵢⱼ encodes how volumes change under parallel transport.
It appears in:
- Einstein's field equations: Gᵢⱼ = Rᵢⱼ - (1/2)Rgᵢⱼ = 8πG Tᵢⱼ
- The Raychaudhuri equation for geodesic congruences
- Energy conditions in general relativity

The scalar curvature R is the trace of the Ricci tensor and gives a single
number characterizing the average curvature at each point.

## Mathematical definition

The Ricci tensor is the contraction of the Riemann tensor:
  Rᵢⱼ = Rᵏᵢₖⱼ = Rᵘᵢᵤⱼ (summing over u)

The scalar curvature is:
  R = gⁱʲRᵢⱼ

## References

* Carroll, S. "Spacetime and Geometry" (2004), Chapter 3
* Wald, R. "General Relativity" (1984), Chapter 3
* O'Neill, B. "Semi-Riemannian Geometry" (1983), Chapter 3

-/

noncomputable section

open Bundle Set Finset Function Filter Module Topology ContinuousLinearMap
open scoped Manifold Bundle

namespace PseudoRiemannianMetric

universe v w

variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type w} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [ChartedSpace H E]
variable {I : ModelWithCorners ℝ E H}
variable {n : WithTop ℕ∞}
variable [IsManifold I (n + 1) M]
variable [inst_tangent_findim : ∀ (x : M), FiniteDimensional ℝ (TangentSpace I x)]

/-!
## The Ricci Tensor

The Ricci tensor is a symmetric (0,2) tensor obtained by contracting the Riemann tensor.
It measures how the volume of a small ball of geodesics changes compared to flat space.

In coordinates: Rᵢⱼ = Rᵏᵢₖⱼ
-/

/-- The Ricci tensor at a point x.

    The Ricci tensor is a symmetric bilinear form that measures volume distortion
    due to curvature. It's obtained by tracing the Riemann tensor.

    Ric(u, v) = tr(w ↦ R(w, u)v)

    In index notation: Rᵢⱼ = Rᵏᵢₖⱼ -/
structure RicciTensorAt (g : PseudoRiemannianMetric E H M n I) (x : M) where
  /-- The Ricci tensor as a bilinear form on the tangent space -/
  toFun : TangentSpace I x → TangentSpace I x → ℝ
  /-- The Ricci tensor is symmetric: Ric(u, v) = Ric(v, u) -/
  symm : ∀ u v, toFun u v = toFun v u
  /-- Linearity in first argument -/
  map_add_left : ∀ u₁ u₂ v, toFun (u₁ + u₂) v = toFun u₁ v + toFun u₂ v
  /-- Linearity in second argument -/
  map_add_right : ∀ u v₁ v₂, toFun u (v₁ + v₂) = toFun u v₁ + toFun u v₂
  /-- Scalar multiplication -/
  map_smul_left : ∀ (c : ℝ) u v, toFun (c • u) v = c * toFun u v
  map_smul_right : ∀ (c : ℝ) u v, toFun u (c • v) = c * toFun u v

namespace RicciTensorAt

variable {g : PseudoRiemannianMetric E H M n I} {x : M}

instance : CoeFun (RicciTensorAt g x)
    (fun _ => TangentSpace I x → TangentSpace I x → ℝ) where
  coe Ric := Ric.toFun

@[simp]
lemma symm' (Ric : RicciTensorAt g x) (u v : TangentSpace I x) :
    Ric u v = Ric v u := Ric.symm u v

@[simp]
lemma add_left (Ric : RicciTensorAt g x) (u₁ u₂ v : TangentSpace I x) :
    Ric (u₁ + u₂) v = Ric u₁ v + Ric u₂ v := Ric.map_add_left u₁ u₂ v

@[simp]
lemma add_right (Ric : RicciTensorAt g x) (u v₁ v₂ : TangentSpace I x) :
    Ric u (v₁ + v₂) = Ric u v₁ + Ric u v₂ := Ric.map_add_right u v₁ v₂

@[simp]
lemma smul_left (Ric : RicciTensorAt g x) (c : ℝ) (u v : TangentSpace I x) :
    Ric (c • u) v = c * Ric u v := Ric.map_smul_left c u v

@[simp]
lemma smul_right (Ric : RicciTensorAt g x) (c : ℝ) (u v : TangentSpace I x) :
    Ric u (c • v) = c * Ric u v := Ric.map_smul_right c u v

@[simp]
lemma zero_left (Ric : RicciTensorAt g x) (v : TangentSpace I x) :
    Ric 0 v = 0 := by
  have h := Ric.map_smul_left 0 0 v
  simp only [zero_smul, zero_mul] at h
  exact h

@[simp]
lemma zero_right (Ric : RicciTensorAt g x) (u : TangentSpace I x) :
    Ric u 0 = 0 := by
  rw [Ric.symm']
  exact zero_left Ric u

/-- The Ricci tensor as a bilinear form -/
def toBilinForm (Ric : RicciTensorAt g x) : LinearMap.BilinForm ℝ (TangentSpace I x) where
  toFun u := {
    toFun := fun v => Ric u v
    map_add' := fun v₁ v₂ => Ric.add_right u v₁ v₂
    map_smul' := fun c v => by simp [Ric.smul_right]
  }
  map_add' := fun u₁ u₂ => by
    ext v
    simp [Ric.add_left]
  map_smul' := fun c u => by
    ext v
    simp [Ric.smul_left]

end RicciTensorAt

/-- The Ricci tensor as a field on the manifold. -/
def RicciTensor (g : PseudoRiemannianMetric E H M n I) :=
  ∀ x : M, RicciTensorAt g x

/-- Construct the Ricci tensor from the Riemann tensor by contraction.

    Semiformal: Full construction requires a basis and trace operation.
    Ric(u, v) = Σᵢ R(eᵢ, u, eⁱ, v) where eᵢ is a basis and eⁱ the dual basis. -/
@[sorryful]
noncomputable def ricciTensor (g : PseudoRiemannianMetric E H M n I) :
    RicciTensor g := sorry

/-!
## Scalar Curvature

The scalar curvature R is the trace of the Ricci tensor with respect to the metric:
  R = gⁱʲRᵢⱼ

It gives a single number at each point measuring the average curvature.
-/

/-- The scalar curvature at a point x.

    R = tr_g(Ric) = gⁱʲRᵢⱼ

    This is the trace of the Ricci tensor, computed by contracting with the
    inverse metric. -/
@[sorryful]
noncomputable def scalarCurvatureAt (g : PseudoRiemannianMetric E H M n I)
    (Ric : RicciTensor g) (x : M) : ℝ := sorry

/-- The scalar curvature as a function on the manifold. -/
noncomputable def scalarCurvature (g : PseudoRiemannianMetric E H M n I)
    (Ric : RicciTensor g) : M → ℝ :=
  fun x => scalarCurvatureAt g Ric x

/-!
## Einstein Manifolds

An Einstein manifold is one where the Ricci tensor is proportional to the metric.
This includes spaces of constant curvature.
-/

/-- A pseudo-Riemannian manifold is Einstein if Ric = λg for some constant λ.

    Einstein manifolds include:
    - Flat space (λ = 0)
    - Spheres (λ > 0 for Riemannian)
    - Hyperbolic space (λ < 0 for Riemannian)
    - de Sitter space (λ > 0 for Lorentzian)
    - Anti-de Sitter space (λ < 0 for Lorentzian) -/
def IsEinsteinManifold (g : PseudoRiemannianMetric E H M n I) (Ric : RicciTensor g) (Λ : ℝ) : Prop :=
  ∀ (x : M) (u v : TangentSpace I x), Ric x u v = Λ * g.val x u v

/-- A Ricci-flat manifold has vanishing Ricci tensor.
    This is the vacuum solution to Einstein's equations. -/
def IsRicciFlat (g : PseudoRiemannianMetric E H M n I) (Ric : RicciTensor g) : Prop :=
  IsEinsteinManifold g Ric 0

/-- Ricci-flat is equivalent to being Einstein with λ = 0. -/
lemma ricciFlat_iff_einstein_zero (g : PseudoRiemannianMetric E H M n I)
    (Ric : RicciTensor g) :
    IsRicciFlat g Ric ↔ IsEinsteinManifold g Ric 0 := by
  rfl

/-- For an Einstein manifold with Ric = λg, the scalar curvature is R = nλ
    where n is the dimension. -/
informal_lemma einstein_scalar_curvature where
  deps := [``IsEinsteinManifold, ``scalarCurvature]
  tag := "7A3ES"

/-- In 4 dimensions, the Schwarzschild exterior solution is Ricci-flat. -/
informal_lemma schwarzschild_ricci_flat where
  deps := [``IsRicciFlat]
  tag := "7A3SC"

/-!
## Contracted Bianchi Identity

The contracted Bianchi identity is crucial for the conservation of energy-momentum:
  ∇ᵘGᵤᵥ = 0

This follows from the second (differential) Bianchi identity for the Riemann tensor.
-/

/-- The second (differential) Bianchi identity:
    ∇_λ R^ρ_σμν + ∇_μ R^ρ_σνλ + ∇_ν R^ρ_σλμ = 0

    This is a consequence of the Jacobi identity for covariant derivatives. -/
informal_lemma bianchi_identity_second where
  deps := [``RiemannTensor, ``LeviCivitaConnection]
  tag := "7A3B2"

/-- The contracted Bianchi identity:
    ∇ᵘRᵤᵥ = (1/2)∇ᵥR

    This follows by contracting the second Bianchi identity twice. -/
informal_lemma contracted_bianchi_identity where
  deps := [``RicciTensor, ``scalarCurvature, ``LeviCivitaConnection]
  tag := "7A3CB"

end PseudoRiemannianMetric

end
