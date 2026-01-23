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
open Lorentz
open CategoryTheory
open MatrixGroups

/-- The map from colors of real Lorentz tensors to complex Lorentz tensors. -/
def colorToComplex (c : realLorentzTensor.Color) : complexLorentzTensor.Color :=
  match c with
  | .up => .up
  | .down => .down

/-- The inclusion map from a real vector to a complex vector, depending on the color.
For `.up` colors, uses `inclCongrRealLorentz`.
For `.down` colors, uses `inclCoRealLorentz`. -/
noncomputable def inclRealToComplex (c : realLorentzTensor.Color) :
    (realLorentzTensor 3).FD.obj (Discrete.mk c) →ₛₗ[Complex.ofRealHom]
    complexLorentzTensor.FD.obj (Discrete.mk (colorToComplex c)) :=
  match c with
  | .up => inclCongrRealLorentz
  | .down => inclCoRealLorentz

/-- Maps a real pure tensor to a complex pure tensor by applying `inclRealToComplex`
componentwise. -/
noncomputable def pureToComplex {n} {c : Fin n → realLorentzTensor.Color}
    (p : Pure (realLorentzTensor 3) c) : Pure complexLorentzTensor (colorToComplex ∘ c) :=
  fun i => inclRealToComplex (c i) (p i)

/-- Helper lemma: `inclRealToComplex` is equivariant at a specific index.

This follows from `inclCongrRealLorentz_ρ` (for `.up` colors) and
`inclCoRealLorentz_ρ` (for `.down` colors). -/
lemma inclRealToComplex_equivariant_at {c : realLorentzTensor.Color}
    (Λ : Matrix.SpecialLinearGroup (Fin 2) ℂ)
    (v : (realLorentzTensor 3).FD.obj (Discrete.mk c)) :
    (complexLorentzTensor.FD.obj (Discrete.mk (colorToComplex c))).ρ Λ (inclRealToComplex c v) =
    inclRealToComplex c (((realLorentzTensor 3).FD.obj (Discrete.mk c)).ρ
      (Lorentz.SL2C.toLorentzGroup Λ) v) := by
  cases c
  · exact inclCongrRealLorentz_ρ Λ v
  · exact inclCoRealLorentz_ρ Λ v

/-- The action on pure tensors commutes with `pureToComplex`.

This lemma follows from `inclRealToComplex_equivariant_at` applied componentwise. -/
lemma pureToComplex_equivariant {n : ℕ} {c : Fin n → realLorentzTensor.Color}
    (p : Pure (realLorentzTensor 3) c) (Λ : Matrix.SpecialLinearGroup (Fin 2) ℂ) :
    Λ • pureToComplex p = pureToComplex (Lorentz.SL2C.toLorentzGroup Λ • p) := by
  funext i
  simp only [Function.comp_apply, Pure.actionP_eq, pureToComplex]
  exact inclRealToComplex_equivariant_at Λ (p i)

/-- The inclusion `inclRealToComplex` respects basis representation.
This is the key technical lemma: applying the inclusion and then taking the basis
coefficient gives the same result as taking the real coefficient and complexifying it.

**Proof strategy:**
For `.up` colors: The complex basis is `complexContrBasisFin4`, the real basis is `contrBasisFin`.
Both are reindexed versions of `ofEquivFun` bases. The proof shows that the inclusion preserves
the basis coefficient by unfolding both sides through the reindexing and `ofEquivFun` structure.

For `.down` colors: Analogous to `.up` using `complexCoBasisFin4` and `coBasisFin`. -/
lemma inclRealToComplex_basis_repr (c : realLorentzTensor.Color)
    (v : (realLorentzTensor 3).FD.obj (Discrete.mk c))
    (b : Fin ((realLorentzTensor 3).repDim c)) :
    (complexLorentzTensor.basis (colorToComplex c)).repr (inclRealToComplex c v)
      (Fin.cast (by match c with | .up => rfl | .down => rfl) b) =
    Complex.ofRealHom (((realLorentzTensor 3).basis c).repr v b) := by
  match c with
  | .up =>
    -- The Fin.cast is identity since both dimensions are 4
    -- After unfolding, both sides equal `ofReal (v.toFin1dℝ (finSumFinEquiv.symm b))`
    rfl
  | .down =>
    -- Same reasoning as .up case
    rfl

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

/-- The component of a complexified pure tensor equals the complexification of the real component.

This follows from `inclRealToComplex_basis_repr` applied to each factor. -/
lemma pureToComplex_component {n : ℕ} {c : Fin n → realLorentzTensor.Color}
    (p : Pure (realLorentzTensor 3) c) (b : ComponentIdx (S := realLorentzTensor) c) :
    (pureToComplex p).component (ComponentIdx.complexify b) =
    Complex.ofRealHom (p.component b) := by
  simp only [Pure.component_eq, Function.comp_apply, Complex.ofRealHom_eq_coe]
  rw [Complex.ofReal_prod]
  congr 1
  funext i
  simp only [pureToComplex, ComponentIdx.complexify, Equiv.coe_fn_mk]
  exact inclRealToComplex_basis_repr (c i) (p i) (b i)

/-- Helper lemma for `toComplex_pure`: smul by real on complex tensor gives complex smul. -/
private lemma real_smul_complex_eq {n : ℕ} {c : Fin n → complexLorentzTensor.Color}
    (r : ℝ) (v : complexLorentzTensor.Tensor c) :
    r • v = (Complex.ofRealHom r) • v := rfl

/-- The map `toComplex` sends a pure tensor to the pure tensor with complexified components.

This is the key lemma connecting the basis-based definition of `toComplex` to the
component-wise definition via `pureToComplex`. -/
lemma toComplex_pure {n : ℕ} {c : Fin n → realLorentzTensor.Color}
    (p : Pure (realLorentzTensor 3) c) :
    toComplex p.toTensor = (pureToComplex p).toTensor := by
  -- Show equality by comparing basis representations
  apply (Tensor.basis (colorToComplex ∘ c)).ext_elem
  intro j
  -- Use toComplex_eq_sum_basis to rewrite LHS
  rw [toComplex_eq_sum_basis]
  rw [basis_repr_pure]
  -- Convert ℝ-smul to ℂ-smul explicitly
  simp_rw [real_smul_complex_eq]
  -- Now simp with ℂ-linear lemmas
  simp only [map_sum, LinearEquiv.map_smul, Basis.repr_self]
  -- Evaluate the sum of Finsupp at j
  simp only [Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.coe_smul, Pi.smul_apply,
    smul_eq_mul, Finsupp.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  -- RHS: (basis.repr (pureToComplex p).toTensor) j = (pureToComplex p).component j
  rw [basis_repr_pure]
  -- Use pureToComplex_component
  have h := pureToComplex_component p (ComponentIdx.complexify.symm j)
  simp only [Equiv.apply_symm_apply] at h
  rw [h]

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
lemma toComplex_equivariant {n} {c : Fin n → realLorentzTensor.Color}
    (v : ℝT(3, c)) (Λ : SL(2, ℂ)) :
    Λ • (toComplex v) = toComplex (Lorentz.SL2C.toLorentzGroup Λ • v) := by
  -- Use induction on pure tensors
  apply Tensor.induction_on_pure (t := v)
  · intro p
    -- Rewrite LHS: toComplex p.toTensor = (pureToComplex p).toTensor
    rw [toComplex_pure p]
    -- Rewrite LHS: Λ • (pureToComplex p).toTensor = (Λ • pureToComplex p).toTensor
    rw [actionT_pure]
    -- Rewrite LHS: (Λ • pureToComplex p) = pureToComplex (toLorentzGroup Λ • p)
    rw [pureToComplex_equivariant]
    -- Rewrite RHS: toLorentzGroup Λ • p.toTensor = (toLorentzGroup Λ • p).toTensor
    rw [actionT_pure]
    -- RHS: toComplex (toLorentzGroup Λ • p).toTensor = (pureToComplex (... Λ • p)).toTensor
    rw [toComplex_pure]
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

/-- Helper lemma: `inclRealToComplex` commutes with `eqToHom` maps.
When colors are equal, applying `inclRealToComplex` after casting by `eqToHom` on the real side
gives the same result as applying `inclRealToComplex` first and then casting by `eqToHom`
on the complex side. -/
lemma inclRealToComplex_eqToHom {c c' : realLorentzTensor.Color} (heq : c = c')
    (v : (realLorentzTensor 3).FD.obj (Discrete.mk c)) :
    inclRealToComplex c' ((realLorentzTensor 3).FD.map (eqToHom (by rw [heq])) v) =
    complexLorentzTensor.FD.map (eqToHom (by simp only [heq, colorToComplex]))
      (inclRealToComplex c v) := by
  subst heq
  simp only [eqToHom_refl]
  rfl

/-- `pureToComplex` commutes with `permP` (index permutation for pure tensors).

The key insight is that `inclRealToComplex` commutes with the `eqToHom` casting maps
that arise from the permutation condition. -/
lemma pureToComplex_permP {n m : ℕ} {c : Fin n → realLorentzTensor.Color}
    {c1 : Fin m → realLorentzTensor.Color}
    {σ : Fin m → Fin n} (h : PermCond c c1 σ) (p : Pure (realLorentzTensor 3) c) :
    pureToComplex (p.permP σ h) = (pureToComplex p).permP σ (colorToComplex_permCond h) := by
  funext i
  simp only [pureToComplex, Pure.permP, Function.comp_apply]
  have hcolor : c (σ i) = c1 i := h.2 i
  have h1 := inclRealToComplex_eqToHom hcolor (p (σ i))
  convert h1 using 2

lemma permT_toComplex {n m} {c : Fin n → realLorentzTensor.Color}
    {c1 : Fin m → realLorentzTensor.Color}
    {σ : Fin m → Fin n} (h : PermCond c c1 σ) (v : ℝT(3, c)) :
    toComplex (permT σ h v) = permT σ (colorToComplex_permCond h) (toComplex v) := by
  -- Use induction on pure tensors
  apply Tensor.induction_on_pure (t := v)
  · intro p
    -- For pure tensors: permT maps to permP, and toComplex maps to pureToComplex
    rw [permT_pure, toComplex_pure]
    conv_rhs => rw [toComplex_pure, permT_pure]
    -- Use pureToComplex_permP
    rw [pureToComplex_permP]
  · intro r t ht
    -- Scalar case: use linearity
    simp only [map_smul, LinearMap.map_smulₛₗ, Complex.ofRealHom_eq_coe, ht]
  · intro t1 t2 ht1 ht2
    -- Addition case: use additivity
    simp only [map_add, ht1, ht2]

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

/-- The complexLorentzTensor FD functor maps compositions of morphisms to
compositions of the corresponding linear maps. -/
private lemma FD_map_comp_apply {c1 c2 c3 : complexLorentzTensor.Color}
    (f : Discrete.mk c1 ⟶ Discrete.mk c2) (g : Discrete.mk c2 ⟶ Discrete.mk c3)
    (v : complexLorentzTensor.FD.obj (Discrete.mk c1)) :
    complexLorentzTensor.FD.map g (complexLorentzTensor.FD.map f v) =
    complexLorentzTensor.FD.map (f ≫ g) v := by
  simp only [Functor.map_comp]
  rfl

/-- `pureToComplex` commutes with `prodP` (up to permutation for color adjustment).

The key insight is that `inclRealToComplex_eqToHom` shows the inclusion commutes with
the `eqToHom` maps arising from color equalities, and the composed `eqToHom` maps
simplify via `eqToHom_trans`. -/
lemma pureToComplex_prodP {n1 n2} {c : Fin n1 → realLorentzTensor.Color}
    {c1 : Fin n2 → realLorentzTensor.Color}
    (p1 : Pure (realLorentzTensor 3) c) (p2 : Pure (realLorentzTensor 3) c1) :
    pureToComplex (Pure.prodP p1 p2) =
    (Pure.prodP (pureToComplex p1) (pureToComplex p2)).permP id
      ⟨Function.bijective_id, fun i => by
        simp only [Function.comp_apply, id_eq]
        exact (congrFun (colorToComplex_append c c1) i).symm⟩ := by
  ext i
  simp only [pureToComplex, Pure.permP, id_eq, Function.comp_apply]
  induction i using Fin.addCases with
  | left j =>
    simp only [Pure.prodP_apply_castAdd]
    have hcol : Fin.append c c1 (Fin.castAdd n2 j) = c j := by simp [Fin.append]
    have h := inclRealToComplex_eqToHom hcol.symm (p1 j)
    rw [h, pureToComplex, FD_map_comp_apply, eqToHom_trans]; rfl
  | right j =>
    simp only [Pure.prodP_apply_natAdd]
    have hcol : Fin.append c c1 (Fin.natAdd n1 j) = c1 j := by simp [Fin.append]
    have h := inclRealToComplex_eqToHom hcol.symm (p2 j)
    rw [h, pureToComplex, FD_map_comp_apply, eqToHom_trans]; rfl

/-- The map `toComplex` commutes with `prodT`.

This shows that taking the tensor product and then complexifying gives the same result
as complexifying each factor and then taking their tensor product (up to a trivial
permutation that accounts for the color function composition order). -/
lemma prodT_toComplex {n1 n2} {c : Fin n1 → realLorentzTensor.Color}
    {c1 : Fin n2 → realLorentzTensor.Color} (v1 : ℝT(3, c)) (v2 : ℝT(3, c1)) :
    toComplex (prodT v1 v2) =
      (permT id ⟨Function.bijective_id, fun i => by simp⟩)
        (prodT (toComplex v1) (toComplex v2)) := by
  apply Tensor.induction_on_pure (t := v1)
  · intro p1
    apply Tensor.induction_on_pure (t := v2)
    · intro p2
      simp only [prodT_pure, toComplex_pure, permT_pure]
      congr 1
      exact pureToComplex_prodP p1 p2
    · intro r t2 ht2
      simp only [LinearMap.map_smulₛₗ, Complex.ofRealHom_eq_coe, RingHom.id_apply] at *
      rw [ht2]
    · intro t2a t2b ht2a ht2b
      simp only [LinearMap.map_add] at *
      rw [ht2a, ht2b]
  · intro r t1 ht1
    simp only [LinearMap.smul_apply, LinearMap.map_smulₛₗ, Complex.ofRealHom_eq_coe,
               RingHom.id_apply] at *
    rw [ht1]
  · intro t1a t1b ht1a ht1b
    simp only [map_add, LinearMap.add_apply] at *
    rw [ht1a, ht1b]

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

/-- `pureToComplex` commutes with `dropPair` (index dropping for pure tensors).

This is a direct consequence of the componentwise nature of both operations. -/
lemma pureToComplex_dropPair {n : ℕ} {c : Fin (n + 1 + 1) → realLorentzTensor.Color}
    (i j : Fin (n + 1 + 1)) (hij : i ≠ j)
    (p : Pure (realLorentzTensor 3) c) :
    pureToComplex (Pure.dropPair i j hij p) =
    Pure.dropPair i j hij (pureToComplex p) := by
  ext m
  simp only [pureToComplex, Pure.dropPair, Function.comp_apply]

/-- Helper: The permutation condition for `colorToComplex` applied to `dropPairEmb`.

This shows that the color function composed with `dropPairEmb` commutes appropriately
with `colorToComplex`. -/
lemma colorToComplex_dropPairEmb {n : ℕ} {c : Fin (n + 1 + 1) → realLorentzTensor.Color}
    (i j : Fin (n + 1 + 1)) :
    colorToComplex ∘ c ∘ Pure.dropPairEmb i j =
    (colorToComplex ∘ c) ∘ Pure.dropPairEmb i j := by
  rfl

/-- The `colorToComplex` map commutes with `τ` (the duality involution).
This shows that the dual color mapping is preserved by complexification. -/
lemma colorToComplex_τ (c : realLorentzTensor.Color) :
    colorToComplex ((realLorentzTensor 3).τ c) = complexLorentzTensor.τ (colorToComplex c) := by
  cases c <;> rfl

/-- toFin13ℂ of inclCongrRealLorentz is ofReal composed with toFin1dℝ. -/
private lemma toFin13ℂ_inclCongrRealLorentz (v : ContrMod 3) :
    ContrℂModule.toFin13ℂ (inclCongrRealLorentz v) = Complex.ofRealHom ∘ v.toFin1dℝ := by
  rfl

/-- toFin13ℂ of inclCoRealLorentz is ofReal composed with toFin1dℝ. -/
private lemma toFin13ℂ_inclCoRealLorentz (v : CoMod 3) :
    CoℂModule.toFin13ℂ (inclCoRealLorentz v) = Complex.ofRealHom ∘ v.toFin1dℝ := by
  rfl

/-- The contraction applied to complexified vectors equals the complexification
of the real contraction (up case).

For `.up` colors, contraction is via `contrCoContract` (real) and `contrCoContraction` (complex). -/
lemma inclRealToComplex_contr_up
    (v : (realLorentzTensor 3).FD.obj (Discrete.mk realLorentzTensor.Color.up))
    (w : (realLorentzTensor 3).FD.obj (Discrete.mk realLorentzTensor.Color.down)) :
    Lorentz.contrCoContraction.hom ((inclCongrRealLorentz v) ⊗ₜ (inclCoRealLorentz w)) =
    Complex.ofRealHom (Lorentz.contrCoContract.hom (v ⊗ₜ w)) := by
  rw [Lorentz.contrCoContraction_hom_tmul, Lorentz.contrCoContract_hom_tmul]
  simp only [toFin13ℂ_inclCongrRealLorentz, toFin13ℂ_inclCoRealLorentz,
    Complex.ofRealHom_eq_coe, Function.comp_apply, dotProduct]
  rw [Complex.ofReal_sum]
  congr 1
  funext i
  simp only [Complex.ofReal_mul]

/-- The contraction applied to complexified vectors equals the complexification
of the real contraction (down case).

For `.down` colors, contraction is via `coContrContract` (real) and
`coContrContraction` (complex). -/
lemma inclRealToComplex_contr_down
    (v : (realLorentzTensor 3).FD.obj (Discrete.mk realLorentzTensor.Color.down))
    (w : (realLorentzTensor 3).FD.obj (Discrete.mk realLorentzTensor.Color.up)) :
    Lorentz.coContrContraction.hom ((inclCoRealLorentz v) ⊗ₜ (inclCongrRealLorentz w)) =
    Complex.ofRealHom (Lorentz.coContrContract.hom (v ⊗ₜ w)) := by
  rw [Lorentz.coContrContraction_hom_tmul, Lorentz.coContrContract_hom_tmul]
  simp only [toFin13ℂ_inclCoRealLorentz, toFin13ℂ_inclCongrRealLorentz,
    Complex.ofRealHom_eq_coe, Function.comp_apply, dotProduct]
  rw [Complex.ofReal_sum]
  congr 1
  funext i
  simp only [Complex.ofReal_mul]

/-- The contraction applied to complexified vectors equals the complexification
of the real contraction.

For `.up` colors, contraction is via `contrCoContract` (real) and `contrCoContraction` (complex).
For `.down` colors, contraction is via `coContrContract` (real) and `coContrContraction` (complex).
Both compute dot products, and the dot product of complexified real vectors equals the
complexification of the real dot product. -/
lemma inclRealToComplex_contr (c : realLorentzTensor.Color)
    (v : (realLorentzTensor 3).FD.obj (Discrete.mk c))
    (w : (realLorentzTensor 3).FD.obj (Discrete.mk ((realLorentzTensor 3).τ c))) :
    (complexLorentzTensor.contr.app (Discrete.mk (colorToComplex c))).hom
      ((inclRealToComplex c v) ⊗ₜ
       (complexLorentzTensor.FD.map (eqToHom (by rw [colorToComplex_τ]; rfl))
          (inclRealToComplex ((realLorentzTensor 3).τ c) w))) =
    Complex.ofRealHom (((realLorentzTensor 3).contr.app (Discrete.mk c)).hom (v ⊗ₜ w)) := by
  match c with
  | .up => exact inclRealToComplex_contr_up v w
  | .down => exact inclRealToComplex_contr_down v w

/-- The contraction coefficient for complexified pure tensors equals the complexification
of the real contraction coefficient.

This combines `inclRealToComplex_contr` with the eqToHom handling. -/
lemma pureToComplex_contrPCoeff {n : ℕ} {c : Fin (n + 1 + 1) → realLorentzTensor.Color}
    (i j : Fin (n + 1 + 1)) (hij : i ≠ j ∧ realLorentzTensor.τ (c i) = c j)
    (p : Pure (realLorentzTensor 3) c) :
    Pure.contrPCoeff i j (colorToComplex_contrCond hij) (pureToComplex p) =
    Complex.ofRealHom (Pure.contrPCoeff i j hij p) := by
  simp only [Pure.contrPCoeff, pureToComplex, Function.comp_apply]
  have hτ : (realLorentzTensor 3).τ (c i) = c j := hij.2
  have hτ' : c j = (realLorentzTensor 3).τ (c i) := hτ.symm
  -- LHS: contr_ℂ ((incl (c i) (p i)) ⊗ₜ FD.map eqToHom (incl (c j) (p j)))
  -- RHS: ofReal (contr_ℝ (p i ⊗ₜ FD.map eqToHom (p j)))
  -- Use inclRealToComplex_eqToHom with hτ' : c j = τ (c i)
  have heq := inclRealToComplex_eqToHom hτ' (p j)
  -- heq : incl (τ (c i)) (FD.map eqToHom (p j)) = FD.map eqToHom (incl (c j) (p j))
  -- We need to use inclRealToComplex_contr with suitable arguments
  have h := inclRealToComplex_contr (c i) (p i)
    ((realLorentzTensor 3).FD.map (eqToHom (by rw [hτ])) (p j))
  -- Convert goal to use h
  convert h using 2
  -- The goal is now to show the second tensor components match
  -- LHS: FD.map eqToHom (incl (c j) (p j))
  -- RHS: FD.map eqToHom (incl (τ (c i)) (FD.map eqToHom (p j)))
  -- Rewrite using heq: incl (τ (c i)) (FD.map eqToHom (p j)) = FD.map eqToHom (incl (c j) (p j))
  rw [heq]
  -- Now: FD.map eqToHom (incl (c j) (p j)) = FD.map eqToHom (FD.map eqToHom (incl (c j) (p j)))
  -- The tensor products differ only in the second component
  congr 1
  -- Goal: FD.map eqToHom (incl (c j) (p j)) = FD.map eqToHom (FD.map eqToHom (incl (c j) (p j)))
  -- Use ConcreteCategory.comp_apply to combine the two FD.map applications on RHS
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, eqToHom_trans]

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
lemma contrT_toComplex {n} {c : Fin (n + 1 + 1) → realLorentzTensor.Color}
    (i j : Fin (n + 1 + 1)) (hij : i ≠ j ∧ realLorentzTensor.τ (c i) = c j)
    (v : ℝT(3, c)) :
    toComplex (contrT n i j hij v) =
      (permT id ⟨Function.bijective_id, fun k => by simp [Function.comp_apply]⟩)
        (contrT n i j (colorToComplex_contrCond hij) (toComplex v)) := by
  apply Tensor.induction_on_pure (t := v)
  · intro p
    -- Pure tensor case
    -- LHS: toComplex (contrT n i j hij p.toTensor)
    --    = toComplex (contrPCoeff • (dropPair p).toTensor)  [by contrT_pure, Pure.contrP]
    --    = ofReal(contrPCoeff) • toComplex((dropPair p).toTensor)  [by semilinearity]
    -- RHS: permT id (contrT n i j ... (toComplex p.toTensor))
    --    = permT id (contrT n i j ... (pureToComplex p).toTensor)  [by toComplex_pure]
    --    = permT id (contrPCoeff' • (dropPair ...).toTensor)  [by contrT_pure, contrP]
    rw [contrT_pure, Pure.contrP, LinearMap.map_smulₛₗ]
    -- LHS: ofReal(contrPCoeff p) • toComplex((dropPair p).toTensor)
    -- RHS: permT id (contrT n i j ... (toComplex p.toTensor))
    conv_rhs => rw [toComplex_pure]
    -- RHS: permT id (contrT n i j ... (pureToComplex p).toTensor)
    rw [contrT_pure, Pure.contrP, map_smul, permT_pure]
    -- RHS: contrPCoeff (pureToComplex p) • (dropPair (pureToComplex p)).permP.toTensor
    rw [pureToComplex_contrPCoeff, toComplex_pure, pureToComplex_dropPair]
    -- Now: ofReal(...) • (pureToComplex (dropPair p)).toTensor =
    --      ofReal(...) • (dropPair (pureToComplex p)).permP.toTensor
    -- Both dropPair terms are equal since pureToComplex_dropPair shows they're the same
    -- And permP with id is trivial
    rfl
  · intro r t ht
    -- Scalar multiplication case
    simp only [map_smul, LinearMap.map_smulₛₗ, Complex.ofRealHom_eq_coe] at *
    rw [ht]
  · intro t1 t2 ht1 ht2
    -- Addition case
    simp only [map_add] at *
    rw [ht1, ht2]

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

/-- `pureToComplex` commutes with `drop` (index dropping for pure tensors).

This is a direct consequence of the componentwise nature of both operations. -/
lemma pureToComplex_drop {n : ℕ} {c : Fin (n + 1) → realLorentzTensor.Color}
    (i : Fin (n + 1)) (p : Pure (realLorentzTensor 3) c) :
    pureToComplex (Pure.drop p i) =
    Pure.drop (pureToComplex p) i := by
  ext j
  simp only [pureToComplex, Pure.drop, Function.comp_apply]

/-- The evaluation coefficient for complexified pure tensors equals the complexification
of the real evaluation coefficient. -/
lemma pureToComplex_evalPCoeff {n : ℕ} {c : Fin (n + 1) → realLorentzTensor.Color}
    (i : Fin (n + 1)) (b : Fin (realLorentzTensor.repDim (c i)))
    (p : Pure (realLorentzTensor 3) c) :
    Pure.evalPCoeff i (indexCast b) (pureToComplex p) =
    Complex.ofRealHom (Pure.evalPCoeff i b p) := by
  simp only [Pure.evalPCoeff, pureToComplex, Function.comp_apply, indexCast]
  exact inclRealToComplex_basis_repr (c i) (p i) b

/-- `evalT` on a pure tensor equals `evalP`. -/
private lemma evalT_pure_real {n : ℕ} {c : Fin (n + 1) → realLorentzTensor.Color}
    (i : Fin (n + 1)) (b : Fin (realLorentzTensor.repDim (c i)))
    (p : Pure (realLorentzTensor 3) c) :
    evalT i b p.toTensor = p.evalP i b := by
  simp only [evalT, Pure.toTensor]
  change (PiTensorProduct.lift (Pure.evalPMultilinear i b)) (PiTensorProduct.tprod _ p) = _
  simp only [Pure.evalPMultilinear, Pure.evalP, MultilinearMap.coe_mk, PiTensorProduct.lift.tprod]

/-- `evalT` on a pure tensor equals `evalP` (complex version). -/
private lemma evalT_pure_complex {n : ℕ} {c : Fin (n + 1) → complexLorentzTensor.Color}
    (i : Fin (n + 1)) (b : Fin (complexLorentzTensor.repDim (c i)))
    (p : Pure complexLorentzTensor c) :
    evalT i b p.toTensor = p.evalP i b := by
  simp only [evalT, Pure.toTensor]
  change (PiTensorProduct.lift (Pure.evalPMultilinear i b)) (PiTensorProduct.tprod _ p) = _
  simp only [Pure.evalPMultilinear, Pure.evalP, MultilinearMap.coe_mk, PiTensorProduct.lift.tprod]

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
lemma evalT_toComplex {n} {c : Fin (n + 1) → realLorentzTensor.Color}
    (i : Fin (n + 1)) (b : Fin (realLorentzTensor.repDim (c i)))
    (v : ℝT(3, c)) :
    toComplex (evalT i b v) =
      (permT id ⟨Function.bijective_id, fun k => by simp [Function.comp_apply]⟩)
        (evalT i (indexCast b) (toComplex v)) := by
  apply Tensor.induction_on_pure (t := v)
  · intro p
    -- Pure tensor case
    -- LHS: toComplex (evalT i b p.toTensor)
    --    = toComplex (evalPCoeff i b p • (drop p i).toTensor)  [by evalT_pure, evalP]
    --    = ofReal(evalPCoeff) • toComplex((drop p i).toTensor)  [by semilinearity]
    -- RHS: permT id (evalT i (indexCast b) (toComplex p.toTensor))
    --    = permT id (evalT i (indexCast b) (pureToComplex p).toTensor)  [by toComplex_pure]
    --    = permT id (evalPCoeff' • (drop (pureToComplex p) i).toTensor)  [by evalT_pure, evalP]
    rw [evalT_pure_real, Pure.evalP, LinearMap.map_smulₛₗ]
    conv_rhs => rw [toComplex_pure]
    rw [evalT_pure_complex, Pure.evalP, map_smul, permT_pure]
    rw [pureToComplex_evalPCoeff, toComplex_pure, pureToComplex_drop]
    rfl
  · intro r t ht
    -- Scalar multiplication case
    simp only [map_smul, LinearMap.map_smulₛₗ, Complex.ofRealHom_eq_coe] at *
    rw [ht]
  · intro t1 t2 ht1 ht2
    -- Addition case
    simp only [map_add] at *
    rw [ht1, ht2]

end realLorentzTensor
