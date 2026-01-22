# PhysLean Session Report - January 22, 2026

## Summary

This session continued work on formalizing sorryful lemmas in PhysLean, focusing on the `ToComplex` module for real-to-complex tensor conversions and the `Bispinors` module for spinor index raising/lowering operations.

## Build Status

**Full repository build: SUCCESS** (4112 jobs completed)

## Completed Formalizations

### 1. ToComplex.lean - Real to Complex Tensor Conversions

**File:** `PhysLean/Relativity/Tensors/RealTensor/ToComplex.lean`

#### New Infrastructure Added

| Definition/Lemma | Description |
|-----------------|-------------|
| `inclRealToComplex` | Semilinear map from real to complex vectors by color |
| `pureToComplex` | Maps real pure tensors to complex pure tensors componentwise |
| `inclRealToComplex_equivariant_at` | Equivariance of inclusion under SL(2,ℂ) action |
| `pureToComplex_equivariant` | Action commutes with complexification |
| `inclRealToComplex_basis_repr` | Inclusion preserves basis coefficients |
| `pureToComplex_component` | Component preservation under complexification |

#### Lemmas Formally Proved (previously sorryful)

| Lemma | Statement |
|-------|-----------|
| `pureToComplex_permP` | `pureToComplex (p.permP σ h) = (pureToComplex p).permP σ ...` |
| `permT_toComplex` | `toComplex (permT σ h v) = permT σ ... (toComplex v)` |
| `prodT_toComplex` | `toComplex (prodT v1 v2) = permT id ... (prodT (toComplex v1) (toComplex v2))` |
| `contrT_toComplex` | `toComplex (contrT n i j h v) = permT id ... (contrT n i' j' ... (toComplex v))` |
| `evalT_toComplex` | `toComplex (evalT i b v) = permT id ... (evalT i (indexCast b) (toComplex v))` |

#### Helper Lemmas Added

- `inclRealToComplex_contr_up` / `inclRealToComplex_contr_down` - Contraction compatibility
- `toFin13ℂ_inclCongrRealLorentz` / `toFin13ℂ_inclCoRealLorentz` - Basis coordinate helpers
- `pureToComplex_contrPCoeff` / `pureToComplex_dropPair` - Contraction coefficient preservation
- `pureToComplex_drop` / `pureToComplex_evalPCoeff` - Evaluation helpers
- `evalT_pure_real` / `evalT_pure_complex` - Evaluation on pure tensors

### 2. Bispinors/Basic.lean - Spinor Index Operations

**File:** `PhysLean/Relativity/Bispinors/Basic.lean`

#### Lemmas Documented with Informal Proofs

| Lemma | Statement |
|-------|-----------|
| `contrBispinorUp_eq_metric_contr_contrBispinorDown` | `{contrBispinorUp p \| α β = εL \| α α' ⊗ εR \| β β' ⊗ contrBispinorDown p \| α' β'}ᵀ` |
| `coBispinorUp_eq_metric_contr_coBispinorDown` | `{coBispinorUp p \| α β = εL \| α α' ⊗ εR \| β β' ⊗ coBispinorDown p \| α' β'}ᵀ` |

These lemmas show that raising spinor indices (with εL and εR) is the inverse of lowering indices (with εL' and εR'). The proofs require:

1. Metric contraction identities:
   - `{εL | α β ⊗ εL' | β γ = δL | α γ}ᵀ`
   - `{εR | α β ⊗ εR' | β γ = δR | α γ}ᵀ`

2. Unit tensor contraction properties from `UnitTensor.lean`

**Status:** Marked `@[sorryful]` with detailed informal proof documentation. The formal proofs require complex nested tensor manipulations following the pattern from `toDualMap_fromDualMap` in `Dual.lean`, but applied to two indices simultaneously.

### 3. Color/Lift.lean - Functor Infrastructure

**File:** `PhysLean/Relativity/Tensors/Color/Lift.lean`

| Definition | Description |
|------------|-------------|
| `forgetLift` | Natural isomorphism showing `lift ⋙ forget ≅ 𝟭` |

Previously an informal definition, now fully formalized showing that lifting a functor and forgetting the monoidal structure recovers the original functor.

## Technical Notes

### Proof Patterns Used

1. **Tensor Induction:** `Tensor.induction_on_pure` for proving properties by cases on pure tensors, scalar multiplication, and addition.

2. **Basis Representation:** Using `(Tensor.basis _).repr.injective` with `ext b` to reduce tensor equalities to component equalities.

3. **Contraction Manipulation:** Lemmas like `contrT_permT`, `prodT_permT_left/right`, `contrT_comm` for rearranging nested tensor operations.

4. **Metric Contractions:** `contrT_metricTensor_metricTensor_eq_dual_unit` and related lemmas for simplifying metric products to unit tensors.

### Files Modified

| File | Changes |
|------|---------|
| `PhysLean/Relativity/Tensors/RealTensor/ToComplex.lean` | +~200 lines of proofs |
| `PhysLean/Relativity/Bispinors/Basic.lean` | Restructured with informal proofs |
| `PhysLean/Relativity/Tensors/Color/Lift.lean` | Formalized `forgetLift` |

## Remaining Work

The bispinor metric contraction lemmas have detailed informal proofs but await formal proofs. The formal proofs would follow the pattern from `Dual.lean:toDualMap_fromDualMap` but require careful navigation through deeply nested `conv` blocks for two-index tensors.

## Dependencies

Key imports used:
- `PhysLean.Relativity.Tensors.ComplexTensor.Metrics.Lemmas`
- `PhysLean.Relativity.Tensors.ComplexTensor.Vector.Pre.Basic`
- `PhysLean.Relativity.Tensors.UnitTensor`
- `PhysLean.Relativity.Tensors.Dual`
