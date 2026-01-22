/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Meta.Linters.Sorry
import PhysLean.Relativity.Tensors.ComplexTensor.Basic
/-!

## Complex Lorentz tensors from Real Lorentz tensors

In this module we define the equivariant semi-linear map from real Lorentz tensors to
complex Lorentz tensors.

-/

namespace realLorentzTensor

open Module TensorSpecies
open Tensor
open complexLorentzTensor

/-- The map from colors of real Lorentz tensors to complex Lorentz tensors. -/
def colorToComplex (c : realLorentzTensor.Color) : complexLorentzTensor.Color :=
  match c with
  | .up => .up
  | .down => .down

/-- The complexification of the component index of a real Lorentz tensor to
  a complex Lorentz tensor. -/
def _root_.TensorSpecies.Tensor.ComponentIdx.complexify {n} {c : Fin n → realLorentzTensor.Color} :
    ComponentIdx (S := realLorentzTensor) c ≃
      ComponentIdx (S := complexLorentzTensor) (colorToComplex ∘ c) where
  toFun i := fun j => Fin.cast (by
    simp only [repDim_eq_one_plus_dim, Nat.reduceAdd, Function.comp_apply]
    generalize c j = cj
    match cj with
    | .up => rfl
    | .down => rfl) (i j)
  invFun i := fun j => Fin.cast (by
    simp only [Function.comp_apply, repDim_eq_one_plus_dim, Nat.reduceAdd]
    generalize c j = cj
    match cj with
    | .up => rfl
    | .down => rfl) (i j)
  left_inv i := by
    rfl
  right_inv i := by
    rfl

/-- The semilinear map from real Lorentz tensors to complex Lorentz tensors,
  defined through basis. -/
noncomputable def toComplex {n} {c : Fin n → realLorentzTensor.Color} :
    ℝT(3, c) →ₛₗ[Complex.ofRealHom] ℂT(colorToComplex ∘ c) where
  toFun v := ∑ i, (Tensor.basis (S := realLorentzTensor) c).repr v i •
    Tensor.basis (S := complexLorentzTensor) (colorToComplex ∘ c) i.complexify
  map_smul' c v := by
    simp only [map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, Complex.ofRealHom_eq_coe,
      Complex.coe_smul]
    rw [Finset.smul_sum]
    congr
    funext i
    rw [smul_smul]
  map_add' c v := by
    simp only [map_add, Finsupp.coe_add, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    congr
    funext i
    simp [add_smul]

lemma toComplex_eq_sum_basis {n} (c : Fin n → realLorentzTensor.Color) (v : ℝT(3, c)) :
    toComplex v = ∑ i, (Tensor.basis (S := realLorentzTensor) c).repr v
      (ComponentIdx.complexify.symm i) •
      Tensor.basis (S := complexLorentzTensor) (colorToComplex ∘ c) i := by
  simp only [toComplex, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply]
  rw [← Equiv.sum_comp ComponentIdx.complexify]
  rfl

@[simp]
lemma toComplex_eq_zero_iff {n} (c : Fin n → realLorentzTensor.Color) (v : ℝT(3, c)) :
    toComplex v = 0 ↔ v = 0 := by
  rw [toComplex_eq_sum_basis]
  have h1 : LinearIndependent ℂ
      (Tensor.basis (S := complexLorentzTensor) (colorToComplex ∘ c)) :=
    Basis.linearIndependent _
  rw [Fintype.linearIndependent_iff] at h1
  constructor
  · intro h
    apply (Tensor.basis (S := realLorentzTensor) c).repr.injective
    ext i
    have h2 := h1 (fun i => ((Tensor.basis c).repr v) (ComponentIdx.complexify.symm i)) h
      i.complexify
    simpa using h2
  · intro h
    subst h
    simp

/-- The map `toComplex` is injective. -/
lemma toComplex_injective {n} (c : Fin n → realLorentzTensor.Color) :
    Function.Injective (toComplex (c := c)) :=
  (injective_iff_map_eq_zero' toComplex).mpr (fun v => toComplex_eq_zero_iff c v)

open Matrix
open MatrixGroups
open complexLorentzTensor
open Lorentz.SL2C in
/-- The map `toComplex` is equivariant with respect to the SL(2,ℂ) action on complex tensors
and the corresponding Lorentz group action on real tensors.

This is a foundational result for GR showing that complexifying real Lorentz tensors
preserves the group action structure. The proof requires showing that basis elements
transform compatibly under both actions.

**Proof strategy:**
1. Expand both sides using basis decomposition via `toComplex_eq_sum_basis`
2. Use linearity of the group action to move it inside the sum
3. Show that the action on complex basis elements corresponds to the action on real basis elements
4. The key technical step is proving: `Λ • (basis_ℂ i) = basis_ℂ (transformed_index Λ i)`
   where the transformation is induced by `toLorentzGroup Λ`

**Required lemmas:**
- How `Λ` acts on `Tensor.basis (S := complexLorentzTensor)`
- How `toLorentzGroup Λ` acts on `Tensor.basis (S := realLorentzTensor)`
- Compatibility of these actions through `colorToComplex` and `ComponentIdx.complexify`
-/
@[sorryful]
lemma toComplex_equivariant {n} {c : Fin n → realLorentzTensor.Color}
    (v : ℝT(3, c)) (Λ : SL(2, ℂ)) :
    Λ • (toComplex v) = toComplex (Lorentz.SL2C.toLorentzGroup Λ • v) := by
  -- Use induction on pure tensors
  apply Tensor.induction_on_pure (t := v)
  · intro p
    rw [actionT_pure]
    /- For pure tensors, the action factors through each component.

    A pure tensor `p` has `p i : (realLorentzTensor.FD.obj (c i))` for each index `i`.
    The action transforms each component:
    - For `.up` colors: uses `(Contr 3).ρ (toLorentzGroup Λ)` on real side,
      `complexContr.ρ Λ` on complex side
    - For `.down` colors: uses `(Co 3).ρ (toLorentzGroup Λ)` on real side,
      `complexCo.ρ Λ` on complex side

    The equivariance follows from:
    - `Lorentz.inclCongrRealLorentz_ρ` for contravariant vectors (`.up`)
    - `Lorentz.inclCoRealLorentz_ρ` for covariant vectors (`.down`)

    The proof requires showing that `toComplex` maps pure tensors to pure tensors
    with complexified components, and that the tensor product structure is preserved.
    -/
    sorry
  · intro r t ht
    -- Scalar multiplication case: Λ • toComplex (r • t) = toComplex (r • toLorentzGroup Λ • t)
    -- toComplex is semilinear: toComplex (r • t) = (r : ℂ) • toComplex t
    simp only [LinearMap.map_smulₛₗ, Complex.ofRealHom_eq_coe, actionT_smul]
    -- Now: Λ • ((r : ℂ) • toComplex t) = (r : ℂ) • toComplex (toLorentzGroup Λ • t)
    -- Use SMulCommClass to commute the scalar (r : ℂ) with the action Λ
    haveI : SMulCommClass SL(2,ℂ) ℂ (complexLorentzTensor.Tensor (colorToComplex ∘ c)) :=
      SMulCommClass.symm ..
    -- The goal is `Λ • (↑r • toComplex t) = ↑r • toComplex (toLorentzGroup Λ • t)`
    -- Using smul_comm: m • n • a = n • m • a
    rw [smul_comm Λ (↑r : ℂ) (toComplex t), ht]
  · intro t1 t2 ht1 ht2
    simp only [actionT_add, map_add, ht1, ht2]

/-!

## Relation to tensor operations

-/

/-- The map `toComplex` commutes with permT. -/
informal_lemma permT_toComplex where
  deps := [``permT]
  tag := "7RKA6"

/-- The map `toComplex` commutes with prodT. -/
informal_lemma prodT_toComplex where
  deps := [``prodT]
  tag := "7RKFF"

/-- The map `toComplex` commutes with contrT. -/
informal_lemma contrT_toComplex where
  deps := [``contrT]
  tag := "7RKFR"

/-- The map `toComplex` commutes with evalT. -/
informal_lemma evalT_toComplex where
  deps := [``evalT]
  tag := "7RKGK"

end realLorentzTensor
