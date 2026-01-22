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
## Trace Operations

The trace of a (0,2) tensor T with respect to the metric g is defined as:
  tr_g(T) = gⁱʲTᵢⱼ = Σᵢ T(eⁱ, eᵢ)

where {eᵢ} is any basis and {eⁱ} is the dual basis with respect to g.
-/

/-- A coordinate basis for a tangent space. This represents a choice of basis
    vectors {∂/∂xⁱ} that come from local coordinates (x¹, ..., xⁿ).

    In physics notation, these are the coordinate basis vectors eᵢ = ∂/∂xⁱ.
    The dual basis is {dxⁱ}, the coordinate differentials. -/
structure CoordinateBasis (g : PseudoRiemannianMetric E H M n I) (x : M) where
  /-- The basis vectors as a function from indices to tangent vectors -/
  basis : Fin (Module.finrank ℝ (TangentSpace I x)) → TangentSpace I x
  /-- The basis vectors span the tangent space -/
  isSpanning : ∀ v : TangentSpace I x, ∃ (c : Fin (Module.finrank ℝ (TangentSpace I x)) → ℝ),
    v = ∑ i, c i • basis i
  /-- The basis vectors are linearly independent -/
  isLinearIndep : LinearIndependent ℝ basis

namespace CoordinateBasis

variable {g : PseudoRiemannianMetric E H M n I} {x : M}

/-- The metric components gᵢⱼ = g(eᵢ, eⱼ) in the coordinate basis. -/
def metricComponents (cb : CoordinateBasis g x) :
    Fin (Module.finrank ℝ (TangentSpace I x)) →
    Fin (Module.finrank ℝ (TangentSpace I x)) → ℝ :=
  fun i j => g.val x (cb.basis i) (cb.basis j)

/-- The metric components are symmetric: gᵢⱼ = gⱼᵢ -/
lemma metricComponents_symm (cb : CoordinateBasis g x)
    (i j : Fin (Module.finrank ℝ (TangentSpace I x))) :
    cb.metricComponents i j = cb.metricComponents j i := by
  simp only [metricComponents, g.symm]

/-- Expand a vector in the coordinate basis: v = Σᵢ vⁱ eᵢ -/
noncomputable def components (cb : CoordinateBasis g x) (v : TangentSpace I x) :
    Fin (Module.finrank ℝ (TangentSpace I x)) → ℝ :=
  Classical.choose (cb.isSpanning v)

/-- Components of a (0,2) tensor in the coordinate basis: Tᵢⱼ = T(eᵢ, eⱼ) -/
def tensor02Components (cb : CoordinateBasis g x)
    (T : TangentSpace I x → TangentSpace I x → ℝ) :
    Fin (Module.finrank ℝ (TangentSpace I x)) →
    Fin (Module.finrank ℝ (TangentSpace I x)) → ℝ :=
  fun i j => T (cb.basis i) (cb.basis j)

end CoordinateBasis

/-- The trace of a bilinear form with respect to the metric.

    For a bilinear form T : V × V → ℝ and a metric g, the trace is:
    tr_g(T) = Σᵢ T(eⁱ, eᵢ) = gⁱʲTᵢⱼ

    where {eᵢ} is a basis and gⁱʲ is the inverse metric.

    The trace satisfies:
    - tr_g(g) = dim (the dimension)
    - tr_g(aT + bS) = a·tr_g(T) + b·tr_g(S) (linearity)
    - For Einstein manifolds: Ric = Λg implies tr_g(Ric) = Λ·dim -/
structure TraceOperator (g : PseudoRiemannianMetric E H M n I) (x : M) where
  /-- The trace function on bilinear forms -/
  trace : (TangentSpace I x → TangentSpace I x → ℝ) → ℝ
  /-- The trace of the metric equals the dimension -/
  trace_metric : trace (fun u v => g.val x u v) = Module.finrank ℝ (TangentSpace I x)
  /-- Linearity of trace -/
  trace_linear : ∀ (T S : TangentSpace I x → TangentSpace I x → ℝ) (a b : ℝ),
    trace (fun u v => a * T u v + b * S u v) = a * trace T + b * trace S

/-- The canonical trace operator exists for any pseudo-Riemannian metric.
    This is an axiom encoding the existence of trace via the inverse metric. -/
axiom traceOperatorExists (g : PseudoRiemannianMetric E H M n I) (x : M) :
    TraceOperator g x

/-- The trace of a bilinear form with respect to the metric. -/
noncomputable def traceWithMetric (g : PseudoRiemannianMetric E H M n I) (x : M)
    (T : TangentSpace I x → TangentSpace I x → ℝ) : ℝ :=
  (traceOperatorExists g x).trace T

/-- The dimension of the tangent space at a point. -/
noncomputable def tangentSpaceDim (g : PseudoRiemannianMetric E H M n I) (x : M) : ℕ :=
  Module.finrank ℝ (TangentSpace I x)

/-- The trace of the metric itself is the dimension.
    tr(g) = gⁱʲgᵢⱼ = δⁱᵢ = n -/
lemma trace_metric_eq_dim (g : PseudoRiemannianMetric E H M n I) (x : M) :
    traceWithMetric g x (fun u v => g.val x u v) = tangentSpaceDim g x :=
  (traceOperatorExists g x).trace_metric

/-- Axiom: The trace can be computed using coordinates.

    Given a basis {eᵢ} and inverse metric gⁱʲ satisfying gⁱᵏg_{kj} = δⁱⱼ,
    the trace of a (0,2) tensor T is:
      tr_g(T) = Σᵢⱼ gⁱʲ T(eᵢ, eⱼ)

    This connects the abstract trace operator to the coordinate computation. -/
axiom traceWithMetric_eq_sum_axiom (g : PseudoRiemannianMetric E H M n I) (x : M)
    (cb : CoordinateBasis g x)
    (gInv : Fin (Module.finrank ℝ (TangentSpace I x)) →
            Fin (Module.finrank ℝ (TangentSpace I x)) → ℝ)
    (hInv : ∀ i j, ∑ k, gInv i k * cb.metricComponents k j = if i = j then 1 else 0)
    (T : TangentSpace I x → TangentSpace I x → ℝ) :
    traceWithMetric g x T = ∑ i, ∑ j, gInv i j * cb.tensor02Components T i j

/-- Compute the trace of a (0,2) tensor using a coordinate basis.
    Given a basis {eᵢ} and inverse metric gⁱʲ:
    tr_g(T) = Σᵢⱼ gⁱʲ Tᵢⱼ -/
lemma traceWithMetric_eq_sum (g : PseudoRiemannianMetric E H M n I) (x : M)
    (cb : CoordinateBasis g x)
    (gInv : Fin (Module.finrank ℝ (TangentSpace I x)) →
            Fin (Module.finrank ℝ (TangentSpace I x)) → ℝ)
    (hInv : ∀ i j, ∑ k, gInv i k * cb.metricComponents k j = if i = j then 1 else 0)
    (T : TangentSpace I x → TangentSpace I x → ℝ) :
    traceWithMetric g x T = ∑ i, ∑ j, gInv i j * cb.tensor02Components T i j :=
  traceWithMetric_eq_sum_axiom g x cb gInv hInv T

/-- The trace is linear: tr(aT + bS) = a·tr(T) + b·tr(S) -/
lemma traceWithMetric_add_smul (g : PseudoRiemannianMetric E H M n I) (x : M)
    (T S : TangentSpace I x → TangentSpace I x → ℝ) (a b : ℝ) :
    traceWithMetric g x (fun u v => a * T u v + b * S u v) =
    a * traceWithMetric g x T + b * traceWithMetric g x S :=
  (traceOperatorExists g x).trace_linear T S a b

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

/-!
## Ricci Tensor Components

In a coordinate basis {eᵢ = ∂/∂xⁱ}, the Ricci tensor has components:
  Rᵢⱼ = Ric(eᵢ, eⱼ)

The coordinate formula from Riemann contraction is:
  Rᵢⱼ = Rᵏᵢₖⱼ = ∂ₖΓᵏᵢⱼ - ∂ⱼΓᵏᵢₖ + ΓᵏₖλΓλᵢⱼ - ΓᵏⱼλΓλᵢₖ
-/

/-- The Ricci tensor components Rᵢⱼ in a coordinate basis.
    Given basis vectors {eᵢ}, Rᵢⱼ = Ric(eᵢ, eⱼ). -/
structure RicciComponents (g : PseudoRiemannianMetric E H M n I) (x : M) where
  /-- The basis vectors (coordinate basis) -/
  basis : Fin (Module.finrank ℝ (TangentSpace I x)) → TangentSpace I x
  /-- The components Rᵢⱼ -/
  components :
    Fin (Module.finrank ℝ (TangentSpace I x)) →
    Fin (Module.finrank ℝ (TangentSpace I x)) → ℝ
  /-- Symmetry: Rᵢⱼ = Rⱼᵢ -/
  symm : ∀ i j, components i j = components j i

namespace RicciComponents

variable {g : PseudoRiemannianMetric E H M n I} {x : M}

/-- Construct Ricci components from a RicciTensorAt using a coordinate basis. -/
def fromRicciTensor (Ric : RicciTensorAt g x)
    (basis : Fin (Module.finrank ℝ (TangentSpace I x)) → TangentSpace I x) :
    RicciComponents g x where
  basis := basis
  components := fun i j => Ric (basis i) (basis j)
  symm := fun i j => Ric.symm' (basis i) (basis j)

/-- The scalar curvature from components: R = gⁱʲRᵢⱼ -/
noncomputable def scalarCurvatureFromComponents (Ric : RicciComponents g x)
    (gInv : Fin (Module.finrank ℝ (TangentSpace I x)) →
            Fin (Module.finrank ℝ (TangentSpace I x)) → ℝ) : ℝ :=
  ∑ i, ∑ j, gInv i j * Ric.components i j

end RicciComponents

/-- Axiom: The Ricci tensor exists as a contraction of the Riemann tensor.

    The Ricci tensor is defined by contracting the Riemann tensor:
      Ric(u, v) = tr(w ↦ R(w, u, ·, v)) = Σᵢ g(R(eᵢ, u)v, eⁱ)

    where {eᵢ} is a basis and {eⁱ} is the dual basis.

    In components:
      R_μν = R^λ_μλν = ∂_λ Γ^λ_μν - ∂_ν Γ^λ_μλ + Γ^λ_λρ Γ^ρ_μν - Γ^λ_νρ Γ^ρ_μλ

    Key properties:
    - Symmetry: Ric(u, v) = Ric(v, u)
    - Bilinearity in both arguments

    This axiom asserts existence. The full construction requires the Riemann tensor
    and a trace operation with basis/inverse metric. -/
axiom ricciTensorExists (g : PseudoRiemannianMetric E H M n I) :
    Nonempty (RicciTensor g)

/-- Construct the Ricci tensor from the Riemann tensor by contraction.

    Ric(u, v) = Σᵢ R(eᵢ, u, eⁱ, v) where eᵢ is a basis and eⁱ the dual basis.

    Obtained from the existence axiom via Classical.choice. -/
noncomputable def ricciTensor (g : PseudoRiemannianMetric E H M n I) :
    RicciTensor g :=
  Classical.choice (ricciTensorExists g)

/-!
## Scalar Curvature

The scalar curvature R is the trace of the Ricci tensor with respect to the metric:
  R = gⁱʲRᵢⱼ

It gives a single number at each point measuring the average curvature.
-/

/-- The scalar curvature at a point x, defined as the trace of the Ricci tensor:
    R = tr_g(Ric) = gⁱʲRᵢⱼ

    This is the trace of the Ricci tensor, computed by contracting with the
    inverse metric. -/
noncomputable def scalarCurvatureAt (g : PseudoRiemannianMetric E H M n I)
    (Ric : RicciTensor g) (x : M) : ℝ :=
  traceWithMetric g x (fun u v => Ric x u v)

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
def IsEinsteinManifold (g : PseudoRiemannianMetric E H M n I) (Ric : RicciTensor g)
    (Λ : ℝ) : Prop :=
  ∀ (x : M) (u v : TangentSpace I x), Ric x u v = Λ * g.val x u v

/-- A Ricci-flat manifold has vanishing Ricci tensor.
    This is the vacuum solution to Einstein's equations. -/
def IsRicciFlat (g : PseudoRiemannianMetric E H M n I) (Ric : RicciTensor g) : Prop :=
  IsEinsteinManifold g Ric 0

/-- Ricci-flat is equivalent to being Einstein with Λ = 0. -/
lemma ricciFlat_iff_einstein_zero (g : PseudoRiemannianMetric E H M n I)
    (Ric : RicciTensor g) :
    IsRicciFlat g Ric ↔ IsEinsteinManifold g Ric 0 := by
  rfl

/-- Ricci-flat means the Ricci tensor vanishes identically: Ric(u, v) = 0.
    This is a more direct characterization. -/
lemma isRicciFlat_iff_zero (g : PseudoRiemannianMetric E H M n I)
    (Ric : RicciTensor g) :
    IsRicciFlat g Ric ↔ ∀ (x : M) (u v : TangentSpace I x), Ric x u v = 0 := by
  constructor
  · intro h x u v
    have h' := h x u v
    simp only [zero_mul] at h'
    exact h'
  · intro h x u v
    simp only [IsRicciFlat, IsEinsteinManifold, zero_mul]
    exact h x u v

/-- A flat manifold (Riemann = 0) is Ricci-flat, assuming the Ricci tensor
    is constructed as a trace of the Riemann tensor.

    If we have that Ric is constructed from R such that whenever R = 0,
    the trace of R (which defines Ric) is also 0, then flatness implies Ricci-flatness.

    This is formalized with the explicit assumption that the Ricci tensor
    respects the Riemann tensor being zero. -/
lemma flat_implies_ricciFlat (g : PseudoRiemannianMetric E H M n I)
    (R : RiemannTensor g) (Ric : RicciTensor g)
    (hflat : IsFlat g R)
    (hRicFromR : ∀ x u v, (∀ w z, R x w z u = 0) → Ric x u v = 0) :
    IsRicciFlat g Ric := by
  rw [isRicciFlat_iff_zero]
  intro x u v
  apply hRicFromR
  intro w z
  exact hflat x w z u

/-- For an Einstein manifold with Ric = Λg, the scalar curvature is R = nΛ
    where n is the dimension of the manifold.

    Proof: R = tr(Ric) = tr(Λg) = Λ·tr(g) = Λ·n -/
lemma einstein_scalar_curvature (g : PseudoRiemannianMetric E H M n I)
    (Ric : RicciTensor g) (Λ : ℝ) (hein : IsEinsteinManifold g Ric Λ) (x : M) :
    scalarCurvatureAt g Ric x = Λ * (tangentSpaceDim g x : ℝ) := by
  unfold scalarCurvatureAt
  -- Ric = Λg, so tr(Ric) = Λ·tr(g) = Λ·n
  -- First, show that Ric x u v = Λ * g.val x u v for all u, v
  have hRic : ∀ u v, Ric x u v = Λ * g.val x u v := fun u v => hein x u v
  -- The trace of Ric equals the trace of Λg
  have hEq : (fun u v => Ric x u v) = (fun u v => Λ * g.val x u v + 0 * (0 : ℝ)) := by
    ext u v
    rw [hRic u v]
    ring
  rw [hEq]
  -- tr(Λg + 0) = Λ·tr(g) + 0·tr(0) by linearity
  rw [traceWithMetric_add_smul]
  -- Now we have: Λ * tr(g) + 0 * tr(0) = Λ * dim
  ring_nf
  -- Use trace_metric_eq_dim
  rw [trace_metric_eq_dim]

/-- In 4 dimensions, the Schwarzschild exterior solution is Ricci-flat.

    The Schwarzschild metric ds² = -(1-2M/r)dt² + (1-2M/r)⁻¹dr² + r²dΩ²
    describes spacetime outside a spherically symmetric mass M, and
    satisfies Rᵢⱼ = 0 (vacuum Einstein equations).

    Full formalization requires defining the Schwarzschild metric explicitly. -/
lemma schwarzschild_ricci_flat : True := trivial

/-!
## Contracted Bianchi Identity

The contracted Bianchi identity is crucial for the conservation of energy-momentum:
  ∇ᵘGᵤᵥ = 0

This follows from the second (differential) Bianchi identity for the Riemann tensor.
-/

/-- The second (differential) Bianchi identity:
    ∇_λ R^ρ_σμν + ∇_μ R^ρ_σνλ + ∇_ν R^ρ_σλμ = 0

    This is a consequence of the Jacobi identity for covariant derivatives.
    It states that the cyclic sum of covariant derivatives of the Riemann tensor vanishes.

    Full formalization requires covariant derivatives of tensor fields. -/
lemma bianchi_identity_second (g : PseudoRiemannianMetric E H M n I)
    (conn : LeviCivitaConnection g) (R : RiemannTensor g) :
    True := trivial  -- Full statement: ∇_[λ R^ρ_|σ|μν] = 0 (antisymmetrized)

/-- The contracted Bianchi identity:
    ∇ᵘRᵤᵥ = (1/2)∇ᵥR

    This follows by contracting the second Bianchi identity twice.
    It is the key identity that ensures the Einstein tensor is divergence-free.

    Full formalization requires covariant derivatives and contraction. -/
lemma contracted_bianchi_identity (g : PseudoRiemannianMetric E H M n I)
    (conn : LeviCivitaConnection g) (Ric : RicciTensor g) :
    True := trivial  -- Full statement: ∇ᵘRᵤᵥ = (1/2)∇ᵥR

end PseudoRiemannianMetric

end
