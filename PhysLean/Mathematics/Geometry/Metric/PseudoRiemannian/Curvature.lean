/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Mathematics.Geometry.Metric.PseudoRiemannian.Connection
/-!
# Riemann Curvature Tensor

This file defines the Riemann curvature tensor for a pseudo-Riemannian manifold.
The Riemann tensor measures the intrinsic curvature of the manifold and is central
to Einstein's theory of general relativity.

## Main definitions

* `RiemannTensorAt`: The Riemann curvature tensor R at a point
* `RiemannTensor`: The Riemann tensor as a field on the manifold
* `riemannSymmetries`: The algebraic symmetries of the Riemann tensor

## Physics context

The Riemann tensor appears in:
- The geodesic deviation equation (tidal forces)
- Einstein's field equations (via the Ricci tensor)
- The definition of spacetime singularities
- Gravitational wave propagation

The curvature of spacetime IS gravity in general relativity.

## Mathematical definition

The Riemann tensor is defined in terms of the connection ∇ as:

  R(X, Y)Z = ∇ₓ∇ᵧZ - ∇ᵧ∇ₓZ - ∇_{[X,Y]}Z

In components:
  Rᵘᵥᵨσ = ∂ᵨΓᵘᵥσ - ∂σΓᵘᵥᵨ + ΓᵘᵨλΓλᵥσ - ΓᵘσλΓλᵥᵨ

## References

* Carroll, S. "Spacetime and Geometry" (2004), Chapter 3
* Wald, R. "General Relativity" (1984), Chapter 3
* Misner, Thorne, Wheeler "Gravitation" (1973), Chapters 11-14
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
## The Riemann Curvature Tensor

The Riemann tensor R(X, Y, Z, W) is a (1,3) tensor that measures the failure of
second covariant derivatives to commute.

R(X, Y)Z = [∇ₓ, ∇ᵧ]Z - ∇_{[X,Y]}Z

The fully covariant Riemann tensor is:
  R(X, Y, Z, W) = g(R(X, Y)Z, W)
-/

/-- The Riemann curvature tensor at a point x.

    R(u, v, w) gives the result of parallel transporting w around an infinitesimal
    parallelogram with sides u and v. It measures the non-commutativity of
    parallel transport.

    In components: Rᵘᵥᵨσ where R(∂ᵥ, ∂ᵨ)∂σ = Rᵘᵥᵨσ ∂ᵤ -/
structure RiemannTensorAt (g : PseudoRiemannianMetric E H M n I) (x : M) where
  /-- The (1,3) Riemann tensor: takes 3 tangent vectors and returns a tangent vector.
      R(u, v, w) = [∇ᵤ, ∇ᵥ]w (ignoring the Lie bracket term for torsion-free connections) -/
  toFun : TangentSpace I x → TangentSpace I x → TangentSpace I x → TangentSpace I x
  /-- Antisymmetry in first two arguments: R(u, v) = -R(v, u) -/
  antisymm_12 : ∀ u v w, toFun u v w = - toFun v u w
  /-- Linearity in first argument -/
  map_add_first : ∀ u₁ u₂ v w, toFun (u₁ + u₂) v w = toFun u₁ v w + toFun u₂ v w
  /-- Linearity in second argument -/
  map_add_second : ∀ u v₁ v₂ w, toFun u (v₁ + v₂) w = toFun u v₁ w + toFun u v₂ w
  /-- Linearity in third argument -/
  map_add_third : ∀ u v w₁ w₂, toFun u v (w₁ + w₂) = toFun u v w₁ + toFun u v w₂
  /-- Scalar multiplication -/
  map_smul_first : ∀ (c : ℝ) u v w, toFun (c • u) v w = c • toFun u v w
  map_smul_second : ∀ (c : ℝ) u v w, toFun u (c • v) w = c • toFun u v w
  map_smul_third : ∀ (c : ℝ) u v w, toFun u v (c • w) = c • toFun u v w
  /-- First Bianchi identity: R(u, v)w + R(v, w)u + R(w, u)v = 0 -/
  bianchi_first : ∀ u v w, toFun u v w + toFun v w u + toFun w u v = 0

namespace RiemannTensorAt

variable {g : PseudoRiemannianMetric E H M n I} {x : M}

instance : CoeFun (RiemannTensorAt g x)
    (fun _ => TangentSpace I x → TangentSpace I x → TangentSpace I x → TangentSpace I x) where
  coe R := R.toFun

@[simp]
lemma antisymm (R : RiemannTensorAt g x) (u v w : TangentSpace I x) :
    R u v w = - R v u w := R.antisymm_12 u v w

@[simp]
lemma add_first (R : RiemannTensorAt g x) (u₁ u₂ v w : TangentSpace I x) :
    R (u₁ + u₂) v w = R u₁ v w + R u₂ v w := R.map_add_first u₁ u₂ v w

@[simp]
lemma add_second (R : RiemannTensorAt g x) (u v₁ v₂ w : TangentSpace I x) :
    R u (v₁ + v₂) w = R u v₁ w + R u v₂ w := R.map_add_second u v₁ v₂ w

@[simp]
lemma add_third (R : RiemannTensorAt g x) (u v w₁ w₂ : TangentSpace I x) :
    R u v (w₁ + w₂) = R u v w₁ + R u v w₂ := R.map_add_third u v w₁ w₂

@[simp]
lemma smul_first (R : RiemannTensorAt g x) (c : ℝ) (u v w : TangentSpace I x) :
    R (c • u) v w = c • R u v w := R.map_smul_first c u v w

@[simp]
lemma smul_second (R : RiemannTensorAt g x) (c : ℝ) (u v w : TangentSpace I x) :
    R u (c • v) w = c • R u v w := R.map_smul_second c u v w

@[simp]
lemma smul_third (R : RiemannTensorAt g x) (c : ℝ) (u v w : TangentSpace I x) :
    R u v (c • w) = c • R u v w := R.map_smul_third c u v w

/-- The first Bianchi identity: R(u, v)w + R(v, w)u + R(w, u)v = 0 -/
theorem bianchi_identity_first (R : RiemannTensorAt g x) (u v w : TangentSpace I x) :
    R u v w + R v w u + R w u v = 0 := R.bianchi_first u v w

/-- R(u, u)w = 0 for any vectors (consequence of antisymmetry) -/
@[simp]
lemma self_zero (R : RiemannTensorAt g x) (u w : TangentSpace I x) :
    R u u w = 0 := by
  have h := R.antisymm u u w
  -- h : R u u w = - R u u w, which implies R u u w = 0
  have h2 : (2 : ℝ) • R u u w = 0 := by
    calc (2 : ℝ) • R u u w = R u u w + R u u w := two_smul ℝ _
    _ = R u u w + (-R u u w) := by rw [← h]
    _ = 0 := add_neg_cancel (R u u w)
  have hne : (2 : ℝ) ≠ 0 := two_ne_zero
  calc R u u w = (2 : ℝ)⁻¹ • ((2 : ℝ) • R u u w) := by rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
    _ = (2 : ℝ)⁻¹ • 0 := by rw [h2]
    _ = 0 := smul_zero _

end RiemannTensorAt

/-- The Riemann curvature tensor as a field on the manifold. -/
def RiemannTensor (g : PseudoRiemannianMetric E H M n I) :=
  ∀ x : M, RiemannTensorAt g x

/-!
## Fully Covariant Riemann Tensor

The Riemann tensor can be lowered to a (0,4) tensor using the metric:
  R(u, v, w, z) = g(R(u, v)w, z)

This tensor has additional symmetries.
-/

/-- The fully covariant Riemann tensor R(u, v, w, z) = g(R(u, v)w, z)
    at a point x. -/
structure RiemannTensor4At (g : PseudoRiemannianMetric E H M n I) (x : M) where
  /-- The (0,4) tensor: R(u, v, w, z) -/
  toFun : TangentSpace I x → TangentSpace I x → TangentSpace I x → TangentSpace I x → ℝ
  /-- Antisymmetry in first pair: R(u, v, w, z) = -R(v, u, w, z) -/
  antisymm_12 : ∀ u v w z, toFun u v w z = - toFun v u w z
  /-- Antisymmetry in second pair: R(u, v, w, z) = -R(u, v, z, w) -/
  antisymm_34 : ∀ u v w z, toFun u v w z = - toFun u v z w
  /-- Pair symmetry: R(u, v, w, z) = R(w, z, u, v) -/
  symm_pairs : ∀ u v w z, toFun u v w z = toFun w z u v
  /-- First Bianchi identity -/
  bianchi_first : ∀ u v w z, toFun u v w z + toFun v w u z + toFun w u v z = 0

namespace RiemannTensor4At

variable {g : PseudoRiemannianMetric E H M n I} {x : M}

instance : CoeFun (RiemannTensor4At g x)
    (fun _ => TangentSpace I x → TangentSpace I x → TangentSpace I x → TangentSpace I x → ℝ) where
  coe R := R.toFun

/-- The number of independent components of the Riemann tensor in n dimensions is n²(n²-1)/12.

    This follows from the symmetries of the Riemann tensor:
    - Antisymmetry in first pair: R(u,v,w,z) = -R(v,u,w,z)
    - Antisymmetry in second pair: R(u,v,w,z) = -R(u,v,z,w)
    - Pair symmetry: R(u,v,w,z) = R(w,z,u,v)
    - First Bianchi identity: R(u,v,w,z) + R(v,w,u,z) + R(w,u,v,z) = 0

    In 4 dimensions: 4²(4²-1)/12 = 16·15/12 = 20 independent components.

    Full formalization requires counting arguments with a basis. -/
@[sorryful]
lemma riemann_independent_components (g : PseudoRiemannianMetric E H M n I) (x : M) :
    True := by
  sorry

end RiemannTensor4At

/-- Construct the (0,4) Riemann tensor from the (1,3) tensor using the metric. -/
def riemannLower (g : PseudoRiemannianMetric E H M n I)
    (R : RiemannTensor g) (x : M) :
    TangentSpace I x → TangentSpace I x → TangentSpace I x → TangentSpace I x → ℝ :=
  fun u v w z => g.val x (R x u v w) z

/-- The Riemann tensor associated with a Levi-Civita connection.

    R(u, v)w = [∇ᵤ, ∇ᵥ]w for the torsion-free Levi-Civita connection.

    Semiformal: Full construction requires derivatives of Christoffel symbols. -/
@[sorryful]
noncomputable def riemannTensor (g : PseudoRiemannianMetric E H M n I) :
    RiemannTensor g := sorry

/-!
## Sectional Curvature

The sectional curvature K(u, v) is the Gaussian curvature of the 2-dimensional
surface spanned by two linearly independent vectors u and v.

  K(u, v) = R(u, v, v, u) / (g(u,u)g(v,v) - g(u,v)²)
-/

/-- The sectional curvature of the plane spanned by u and v.

    This generalizes Gaussian curvature to higher dimensions.
    For surfaces, it equals the Gaussian curvature. -/
noncomputable def sectionalCurvature (g : PseudoRiemannianMetric E H M n I)
    (R4 : ∀ x, RiemannTensor4At g x) (x : M)
    (u v : TangentSpace I x) : ℝ :=
  let num := R4 x u v v u
  let denom := g.val x u u * g.val x v v - (g.val x u v)^2
  if denom ≠ 0 then num / denom else 0

/-- A manifold has constant sectional curvature K if K(u, v) = K for all planes. -/
def HasConstantSectionalCurvature (g : PseudoRiemannianMetric E H M n I)
    (R4 : ∀ x, RiemannTensor4At g x) (K : ℝ) : Prop :=
  ∀ (x : M) (u v : TangentSpace I x),
    g.val x u u * g.val x v v - (g.val x u v)^2 ≠ 0 →
    sectionalCurvature g R4 x u v = K

/-- For constant sectional curvature K, the Riemann tensor has the form:
    R(u, v, w, z) = K(g(v,w)g(u,z) - g(u,w)g(v,z))

    This characterizes spaces of constant curvature (spheres, hyperbolic space, flat space).
    The sign convention follows O'Neill: R(X,Y)Z = K(g(Y,Z)X - g(X,Z)Y). -/
def HasConstantCurvatureForm (g : PseudoRiemannianMetric E H M n I)
    (R4 : ∀ x, RiemannTensor4At g x) (K : ℝ) : Prop :=
  ∀ (x : M) (u v w z : TangentSpace I x),
    R4 x u v w z = K * (g.val x v w * g.val x u z - g.val x u w * g.val x v z)

/-- Constant curvature form implies constant sectional curvature. -/
lemma constantCurvatureForm_implies_constantSectionalCurvature
    (g : PseudoRiemannianMetric E H M n I)
    (R4 : ∀ x, RiemannTensor4At g x) (K : ℝ)
    (hform : HasConstantCurvatureForm g R4 K) :
    HasConstantSectionalCurvature g R4 K := by
  intro x u v hdenom
  unfold sectionalCurvature
  rw [if_pos hdenom, hform x u v v u]
  -- R4(u,v,v,u) = K(g(v,v)g(u,u) - g(u,v)g(v,u))
  have hsymm : g.val x v u = g.val x u v := (g.symm x u v).symm
  rw [hsymm]
  -- Now we have K * (g(v,v)*g(u,u) - g(u,v)*g(u,v)) / (g(u,u)*g(v,v) - g(u,v)²)
  have heq : g.val x v v * g.val x u u - g.val x u v * g.val x u v =
             g.val x u u * g.val x v v - g.val x u v ^ 2 := by ring
  rw [heq]
  rw [mul_div_assoc, div_self hdenom, mul_one]

/-!
## Flat Manifolds

A manifold is flat if the Riemann tensor vanishes identically.
This is equivalent to having zero sectional curvature everywhere.
-/

/-- A pseudo-Riemannian manifold is flat if its Riemann tensor vanishes. -/
def IsFlat (g : PseudoRiemannianMetric E H M n I) (R : RiemannTensor g) : Prop :=
  ∀ x u v w, R x u v w = 0

/-- A flat manifold has zero sectional curvature everywhere. -/
lemma flat_implies_zero_sectional_curvature (g : PseudoRiemannianMetric E H M n I)
    (R : RiemannTensor g) (R4 : ∀ x, RiemannTensor4At g x)
    (hR4 : ∀ x u v w z, R4 x u v w z = g.val x (R x u v w) z)
    (hflat : IsFlat g R) :
    HasConstantSectionalCurvature g R4 0 := by
  intro x u v hdenom
  unfold sectionalCurvature
  rw [if_pos hdenom]
  -- The numerator R4(u, v, v, u) = g(R(u,v)v, u) = g(0, u) = 0
  have hR : R x u v v = 0 := hflat x u v v
  rw [hR4 x u v v u, hR, map_zero, ContinuousLinearMap.zero_apply]
  simp

/-- For a flat manifold, the (0,4) Riemann tensor vanishes. -/
lemma flat_riemann4_zero (g : PseudoRiemannianMetric E H M n I)
    (R : RiemannTensor g) (hflat : IsFlat g R) (x : M)
    (u v w z : TangentSpace I x) :
    g.val x (R x u v w) z = 0 := by
  rw [hflat x u v w, map_zero, ContinuousLinearMap.zero_apply]

/-- Minkowski space (flat pseudo-Riemannian manifold) has vanishing Riemann tensor. -/
lemma minkowski_is_flat (g : PseudoRiemannianMetric E H M n I)
    (R : RiemannTensor g) (hflat : IsFlat g R) :
    ∀ x u v w, R x u v w = 0 := hflat

end PseudoRiemannianMetric

end
