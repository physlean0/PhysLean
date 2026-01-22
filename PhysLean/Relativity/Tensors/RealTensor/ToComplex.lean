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
    simp only [smul_comm, ht]
  · intro t1 t2 ht1 ht2
    simp only [actionT_add, map_add, ht1, ht2]

/-!

## Relation to tensor operations

-/

/-- The `colorToComplex` map preserves permutation conditions.
If `σ` defines a valid permutation of real tensor indices, then it also defines a valid
permutation of the complexified tensor indices. -/
lemma colorToComplex_permCond {n m}
    {c : Fin n → realLorentzTensor.Color} {c1 : Fin m → realLorentzTensor.Color}
    {σ : Fin m → Fin n} (h : PermCond c c1 σ) :
    PermCond (colorToComplex ∘ c) (colorToComplex ∘ c1) σ := by
  constructor
  · exact h.1
  · intro j
    simp only [Function.comp_apply]
    rw [h.2 j]

/-- The map `toComplex` commutes with `permT`.

This shows that permuting indices and then complexifying gives the same result
as complexifying and then permuting (with the same permutation).

**Proof strategy:**
1. Use induction on pure tensors via `Tensor.induction_on_pure`
2. For pure tensors, show that `permP` on real side corresponds to `permP` on complex side
3. The key is showing that `ComponentIdx.complexify` commutes with index permutations
-/
@[sorryful]
lemma permT_toComplex {n m} {c : Fin n → realLorentzTensor.Color}
    {c1 : Fin m → realLorentzTensor.Color}
    {σ : Fin m → Fin n} (h : PermCond c c1 σ) (v : ℝT(3, c)) :
    toComplex (permT σ h v) = permT σ (colorToComplex_permCond h) (toComplex v) := by
  sorry

/-- The `colorToComplex` map commutes with `Fin.append`.
This shows that complexifying colors distributes over index concatenation. -/
lemma colorToComplex_append {n1 n2}
    (c : Fin n1 → realLorentzTensor.Color) (c1 : Fin n2 → realLorentzTensor.Color) :
    colorToComplex ∘ (Fin.append c c1) = Fin.append (colorToComplex ∘ c) (colorToComplex ∘ c1) := by
  funext i
  simp only [Function.comp_apply, Fin.append]
  induction i using Fin.addCases with
  | left l => simp [Fin.addCases]
  | right r => simp [Fin.addCases]

/-- Pointwise version of `colorToComplex_append`. -/
@[simp]
lemma colorToComplex_append_apply {n1 n2}
    (c : Fin n1 → realLorentzTensor.Color) (c1 : Fin n2 → realLorentzTensor.Color)
    (i : Fin (n1 + n2)) :
    colorToComplex (Fin.append c c1 i) =
      Fin.append (colorToComplex ∘ c) (colorToComplex ∘ c1) i := by
  have h := congrFun (colorToComplex_append c c1) i
  simp only [Function.comp_apply] at h
  exact h

/-- The map `toComplex` commutes with `prodT`.

This shows that taking the tensor product and then complexifying gives the same result
as complexifying each factor and then taking their tensor product.

**Proof strategy:**
1. Use bilinearity of `prodT` to reduce to the case of pure tensors
2. For pure tensors, `prodT` corresponds to `prodP` which concatenates components
3. Show that `toComplex` maps pure products to pure products with complexified components
4. Use `colorToComplex_append` to match the color functions
-/
@[sorryful]
lemma prodT_toComplex {n1 n2} {c : Fin n1 → realLorentzTensor.Color}
    {c1 : Fin n2 → realLorentzTensor.Color} (v1 : ℝT(3, c)) (v2 : ℝT(3, c1)) :
    toComplex (prodT v1 v2) =
      (permT id ⟨Function.bijective_id, fun i => by simp⟩)
        (prodT (toComplex v1) (toComplex v2)) := by
  sorry

/-- Helper: `complexLorentzTensor.τ` applied to `.up` gives `.down`. -/
private lemma complexLorentzTensor_τ_up :
    complexLorentzTensor.τ complexLorentzTensor.Color.up = complexLorentzTensor.Color.down := rfl

/-- Helper: `complexLorentzTensor.τ` applied to `.down` gives `.up`. -/
private lemma complexLorentzTensor_τ_down :
    complexLorentzTensor.τ complexLorentzTensor.Color.down = complexLorentzTensor.Color.up := rfl

/-- The `colorToComplex` map preserves the duality condition for contraction.
If `τ_ℝ (c i) = c j` for real colors, then `τ_ℂ ((colorToComplex ∘ c) i) = (colorToComplex ∘ c) j`
for the complexified colors.

This is needed for `contrT_toComplex` to ensure the contraction condition transfers. -/
lemma colorToComplex_contrCond {n} {c : Fin (n + 1 + 1) → realLorentzTensor.Color}
    {i j : Fin (n + 1 + 1)} (hij : i ≠ j ∧ realLorentzTensor.τ (c i) = c j) :
    i ≠ j ∧ complexLorentzTensor.τ ((colorToComplex ∘ c) i) = (colorToComplex ∘ c) j := by
  constructor
  · exact hij.1
  · simp only [Function.comp_apply]
    have h := hij.2
    -- The duality τ swaps .up ↔ .down for both real and complex tensors
    -- So τ_ℂ (colorToComplex c_i) = colorToComplex (τ_ℝ c_i) = colorToComplex c_j
    cases hci : c i with
    | up =>
      cases hcj : c j with
      | up =>
        -- This case is impossible: τ(.up) = .down ≠ .up
        simp only [hci, hcj] at h
        exact absurd h (by decide)
      | down =>
        -- colorToComplex .up = .up, colorToComplex .down = .down
        -- τ_ℂ .up = .down ✓
        simp only [colorToComplex, complexLorentzTensor_τ_up]
    | down =>
      cases hcj : c j with
      | up =>
        -- colorToComplex .down = .down, colorToComplex .up = .up
        -- τ_ℂ .down = .up ✓
        simp only [colorToComplex, complexLorentzTensor_τ_down]
      | down =>
        -- This case is impossible: τ(.down) = .up ≠ .down
        simp only [hci, hcj] at h
        exact absurd h (by decide)

/-- The map `toComplex` commutes with `contrT`.

This shows that contracting indices and then complexifying gives the same result
as complexifying and then contracting (with the transferred contraction condition).

**Proof strategy:**
1. Use induction on pure tensors via `Tensor.induction_on_pure`
2. For pure tensors, contraction involves:
   - Computing the contraction coefficient via the metric pairing
   - Dropping the contracted indices from the pure tensor
3. The key is showing that the contraction coefficient (metric pairing) is preserved:
   - Real metric pairing: `S.contr.hom (v_i ⊗ₜ v_j)` for real vectors
   - Complex metric pairing: same structure for complexified vectors
4. Use `colorToComplex_contrCond` to transfer the duality condition
-/
@[sorryful]
lemma contrT_toComplex {n} {c : Fin (n + 1 + 1) → realLorentzTensor.Color}
    (i j : Fin (n + 1 + 1)) (hij : i ≠ j ∧ realLorentzTensor.τ (c i) = c j)
    (v : ℝT(3, c)) :
    toComplex (contrT n i j hij v) =
      (permT id ⟨Function.bijective_id, fun k => by simp [Function.comp_apply]⟩)
        (contrT n i j (colorToComplex_contrCond hij) (toComplex v)) := by
  sorry

/-- The representation dimension is preserved by `colorToComplex`.
Real and complex Lorentz tensors have the same dimension (4) for each color. -/
lemma repDim_colorToComplex (c : realLorentzTensor.Color) :
    complexLorentzTensor.repDim (colorToComplex c) = realLorentzTensor.repDim c := by
  match c with
  | .up => rfl
  | .down => rfl

/-- Cast an index from the real representation dimension to the complex one. -/
def indexCast {c : realLorentzTensor.Color} (b : Fin (realLorentzTensor.repDim c)) :
    Fin (complexLorentzTensor.repDim (colorToComplex c)) :=
  Fin.cast (repDim_colorToComplex c).symm b

/-- The map `toComplex` commutes with `evalT`.

This shows that evaluating an index and then complexifying gives the same result
as complexifying and then evaluating (with the cast index).

**Proof strategy:**
1. Use induction on pure tensors via `Tensor.induction_on_pure`
2. For pure tensors, evaluation picks out a specific component value
3. The key is showing that:
   - The index `b` on the real side corresponds to `indexCast b` on the complex side
   - The remaining components are complexified correctly
4. Use `repDim_colorToComplex` to relate the index types
-/
@[sorryful]
lemma evalT_toComplex {n} {c : Fin (n + 1) → realLorentzTensor.Color}
    (i : Fin (n + 1)) (b : Fin (realLorentzTensor.repDim (c i)))
    (v : ℝT(3, c)) :
    toComplex (evalT i b v) =
      (permT id ⟨Function.bijective_id, fun k => by simp [Function.comp_apply]⟩)
        (evalT i (indexCast b) (toComplex v)) := by
  sorry

end realLorentzTensor
