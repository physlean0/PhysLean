/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Relativity.PauliMatrices.ToTensor
import PhysLean.Meta.Linters.Sorry
/-!

## Bispinors

-/
open IndexNotation
open CategoryTheory
open MonoidalCategory
open Matrix
open MatrixGroups
open Complex
open TensorProduct
open IndexNotation
open CategoryTheory
open OverColor.Discrete
open Fermion
noncomputable section
namespace complexLorentzTensor
open Lorentz
open PauliMatrix
/-!

## Definitions

-/
open TensorSpecies
open Tensor

/-- A bispinor `pᵃᵃ` created from a lorentz vector `p^μ`. -/
def contrBispinorUp (p : ℂT[.up]) : ℂT[.upL, .upR] := permT id (PermCond.auto)
  {pauliCo | μ α β ⊗ p | μ}ᵀ

/-- A bispinor `pₐₐ` created from a lorentz vector `p^μ`. -/
def contrBispinorDown (p : ℂT[.up]) : ℂT[.downL, .downR] := permT id (PermCond.auto)
  {εL' | α α' ⊗ εR' | β β' ⊗ contrBispinorUp p | α β}ᵀ

/-- A bispinor `pᵃᵃ` created from a lorentz vector `p_μ`. -/
def coBispinorUp (p : ℂT[.down]) : ℂT[.upL, .upR] := permT id (PermCond.auto)
  {σ^^^ | μ α β ⊗ p | μ}ᵀ

/-- A bispinor `pₐₐ` created from a lorentz vector `p_μ`. -/
def coBispinorDown (p : ℂT[.down]) : ℂT[.downL, .downR] := permT id (PermCond.auto)
  {εL' | α α' ⊗ εR' | β β' ⊗ coBispinorUp p | α β}ᵀ

/-!

## Basic equalities.

-/

/-- The relation between `contrBispinorUp` and `contrBispinorDown`:
`{contrBispinorUp p | α β = εL | α α' ⊗ εR | β β' ⊗ contrBispinorDown p | α' β' }ᵀ`.

**Proof strategy:**
1. Expand `contrBispinorDown` using its definition:
   `contrBispinorDown p = permT id ⋯ {εL' | α α' ⊗ εR' | β β' ⊗ contrBispinorUp p | α β}ᵀ`

2. The RHS then becomes:
   `εL | α α' ⊗ εR | β β' ⊗ (εL' | α' α'' ⊗ εR' | β' β'' ⊗ contrBispinorUp p | α'' β'')`

3. Using the metric contraction lemmas:
   - `leftMetric_contr_altLeftMetric : {εL | α β ⊗ εL' | β γ = δL | α γ}ᵀ`
   - `rightMetric_contr_altRightMetric : {εR | α β ⊗ εR' | β γ = δR | α γ}ᵀ`

4. After contraction, we get:
   `δL | α α'' ⊗ δR | β β'' ⊗ contrBispinorUp p | α'' β''`

5. The unit tensor contractions then give back `contrBispinorUp p | α β`.

**Required infrastructure:**
- Tensor contraction associativity lemmas for multiple contractions
- Unit tensor contraction lemmas: `contrT_single_unitTensor`, `contrT_unitTensor_dual_single`
- Permutation compatibility lemmas for the index reordering
-/
@[sorryful]
lemma contrBispinorUp_eq_metric_contr_contrBispinorDown (p : ℂT[.up]) :
    {contrBispinorUp p | α β = εL | α α' ⊗ εR | β β' ⊗ contrBispinorDown p | α' β'}ᵀ := by
  simp only [Tensorial.self_toTensor_apply]
  rw [contrBispinorDown]
  /- The goal becomes:
     contrBispinorUp p =
       (permT ![0, 1] ⋯)
         ((contrT 2 1 3 ⋯)
           ((contrT 4 3 5 ⋯)
             ((prodT ((prodT εL) εR))
               ((permT id ⋯)
                 ((contrT 2 0 3 ⋯)
                   ((contrT 4 2 5 ⋯)
                     ((prodT ((prodT εL') εR')) (contrBispinorUp p))))))))

     The proof requires:
     1. Reordering the products using associativity (prodT_assoc)
     2. Applying metric contraction lemmas to get unit tensors
     3. Using unit tensor contractions to recover contrBispinorUp p
     4. Showing the permutations compose to the identity
  -/
  sorry

/-- The relation between `coBispinorUp` and `coBispinorDown`:
`{coBispinorUp p | α β = εL | α α' ⊗ εR | β β' ⊗ coBispinorDown p | α' β' }ᵀ`.

**Proof strategy:** (Analogous to `contrBispinorUp_eq_metric_contr_contrBispinorDown`)
1. Expand `coBispinorDown` using its definition:
   `coBispinorDown p = permT id ⋯ {εL' | α α' ⊗ εR' | β β' ⊗ coBispinorUp p | α β}ᵀ`

2. The RHS then becomes:
   `εL | α α' ⊗ εR | β β' ⊗ (εL' | α' α'' ⊗ εR' | β' β'' ⊗ coBispinorUp p | α'' β'')`

3. Using the metric contraction lemmas:
   - `leftMetric_contr_altLeftMetric : {εL | α β ⊗ εL' | β γ = δL | α γ}ᵀ`
   - `rightMetric_contr_altRightMetric : {εR | α β ⊗ εR' | β γ = δR | α γ}ᵀ`

4. After contraction, we get:
   `δL | α α'' ⊗ δR | β β'' ⊗ coBispinorUp p | α'' β''`

5. The unit tensor contractions then give back `coBispinorUp p | α β`.
-/
@[sorryful]
lemma coBispinorUp_eq_metric_contr_coBispinorDown (p : ℂT[.down]) :
    {coBispinorUp p | α β = εL | α α' ⊗ εR | β β' ⊗ coBispinorDown p | α' β'}ᵀ := by
  simp only [Tensorial.self_toTensor_apply]
  rw [coBispinorDown]
  sorry

end complexLorentzTensor
end
