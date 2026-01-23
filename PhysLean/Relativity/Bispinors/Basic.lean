/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Relativity.PauliMatrices.ToTensor
import PhysLean.Relativity.Tensors.ComplexTensor.Metrics.Lemmas
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
`{contrBispinorUp p | α β = εL | α α' ⊗ εR | β β' ⊗ contrBispinorDown p | α' β'}ᵀ`.

This lemma shows that raising indices (with εL and εR) is the inverse of lowering indices
(with εL' and εR'). The proof uses the metric contraction identities:
- `{εL | α β ⊗ εL' | β γ = δL | α γ}ᵀ`
- `{εR | α β ⊗ εR' | β γ = δR | α γ}ᵀ`
And the unit tensor contraction properties.

**Informal proof:**
1. Expand contrBispinorDown: `εL' | α' α'' ⊗ εR' | β' β'' ⊗ contrBispinorUp p | α'' β''`
2. RHS becomes: `εL | α α' ⊗ εR | β β' ⊗ εL' | α' α'' ⊗ εR' | β' β'' ⊗ contrBispinorUp p | α'' β''`
3. Group and contract: `(εL ⊗ εL')_{α α''} = δL_{α α''}` and `(εR ⊗ εR')_{β β''} = δR_{β β''}`
4. Result: `δL | α α'' ⊗ δR | β β'' ⊗ contrBispinorUp p | α'' β''`
5. Unit tensor contractions give back: `contrBispinorUp p | α β`
-/
@[sorryful]
lemma contrBispinorUp_eq_metric_contr_contrBispinorDown (p : ℂT[.up]) :
    {contrBispinorUp p | α β = εL | α α' ⊗ εR | β β' ⊗ contrBispinorDown p | α' β'}ᵀ := by
  simp only [Tensorial.self_toTensor_apply]
  rw [contrBispinorDown]
  /- The proof requires careful manipulation of the nested tensor structure.
     The key steps are:
     1. Use prodT_permT_right to move the inner permT through the product
     2. Use contrT_permT to move permutations past contractions
     3. Rearrange products to group εL with εL' and εR with εR'
     4. Apply leftMetric_contr_altLeftMetric and rightMetric_contr_altRightMetric
     5. Use contrT_unitTensor_dual_single to eliminate the unit tensors

     This follows the pattern from toDualMap_fromDualMap in Dual.lean,
     but applied to two indices simultaneously.
  -/
  sorry

/-- The relation between `coBispinorUp` and `coBispinorDown`:
`{coBispinorUp p | α β = εL | α α' ⊗ εR | β β' ⊗ coBispinorDown p | α' β'}ᵀ`.

This lemma is analogous to `contrBispinorUp_eq_metric_contr_contrBispinorDown` but for
covariant Lorentz vectors. It shows that raising indices (with εL and εR) is the inverse
of lowering indices (with εL' and εR').

**Informal proof:**
1. Expand coBispinorDown: `εL' | α' α'' ⊗ εR' | β' β'' ⊗ coBispinorUp p | α'' β''`
2. RHS becomes: `εL | α α' ⊗ εR | β β' ⊗ εL' | α' α'' ⊗ εR' | β' β'' ⊗ coBispinorUp p | α'' β''`
3. Group and contract: `(εL ⊗ εL')_{α α''} = δL_{α α''}` and `(εR ⊗ εR')_{β β''} = δR_{β β''}`
4. Result: `δL | α α'' ⊗ δR | β β'' ⊗ coBispinorUp p | α'' β''`
5. Unit tensor contractions give back: `coBispinorUp p | α β`

The proof uses the metric contraction identities:
- `{εL | α β ⊗ εL' | β γ = δL | α γ}ᵀ`
- `{εR | α β ⊗ εR' | β γ = δR | α γ}ᵀ`
And the unit tensor contraction properties.
-/
@[sorryful]
lemma coBispinorUp_eq_metric_contr_coBispinorDown (p : ℂT[.down]) :
    {coBispinorUp p | α β = εL | α α' ⊗ εR | β β' ⊗ coBispinorDown p | α' β'}ᵀ := by
  simp only [Tensorial.self_toTensor_apply]
  rw [coBispinorDown]
  /- The proof is analogous to contrBispinorUp_eq_metric_contr_contrBispinorDown.
     It requires careful manipulation of the nested tensor structure using:
     - prodT_permT_right to move the inner permT through the product
     - contrT_permT to move permutations past contractions
     - leftMetric_contr_altLeftMetric and rightMetric_contr_altRightMetric
     - contrT_unitTensor_dual_single to eliminate the unit tensors
  -/
  sorry

end complexLorentzTensor
end
