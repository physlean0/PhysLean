/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Geometry.Manifold.Instances.Real
import PhysLean.Meta.Informal.SemiFormal
import PhysLean.SpaceAndTime.SpaceTime.Basic
/-!
# The Standard Model

This file defines the basic properties of the standard model in particle physics.

-/
TODO "6V2FP" "Redefine the gauge group as a quotient of SU(3) x SU(2) x U(1) by a subgroup of ℤ₆."

namespace StandardModel

open Manifold
open Matrix
open Complex
open ComplexConjugate

/-- The global gauge group of the Standard Model with no discrete quotients.
  The `I` in the Name is an indication of the statement that this has no discrete quotients. -/
abbrev GaugeGroupI : Type :=
  specialUnitaryGroup (Fin 3) ℂ × specialUnitaryGroup (Fin 2) ℂ × unitary ℂ

namespace GaugeGroupI

/-- The underlying element of `SU(3)` of an element in `GaugeGroupI`. -/
def toSU3 : GaugeGroupI →* specialUnitaryGroup (Fin 3) ℂ where
  toFun g := g.1
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The underlying element of `SU(2)` of an element in `GaugeGroupI`. -/
def toSU2 : GaugeGroupI →* specialUnitaryGroup (Fin 2) ℂ where
  toFun g := g.2.1
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The underlying element of `U(1)` of an element in `GaugeGroupI`. -/
def toU1 : GaugeGroupI →* unitary ℂ where
  toFun g := g.2.2
  map_one' := rfl
  map_mul' _ _ := rfl

@[ext]
lemma ext {g g' : GaugeGroupI} (hSU3 : toSU3 g = toSU3 g')
    (hSU2 : toSU2 g = toSU2 g') (hU1 : toU1 g = toU1 g') : g = g' := by
  rcases g with ⟨g1, g2, g3⟩
  cases g'
  simp only [toSU3, toSU2, toU1] at hSU3 hSU2 hU1
  simp_all

instance : Star GaugeGroupI where
  star g := (star g.1, star g.2.1, star g.2.2)

lemma star_eq (g : GaugeGroupI) : star g = (star g.1, star g.2.1, star g.2.2) := rfl

@[simp]
lemma star_toSU3 (g : GaugeGroupI) : toSU3 (star g) = star (toSU3 g) := rfl

@[simp]
lemma star_toSU2 (g : GaugeGroupI) : toSU2 (star g) = star (toSU2 g) := rfl

@[simp]
lemma star_toU1 (g : GaugeGroupI) : toU1 (star g) = star (toU1 g) := rfl

instance : InvolutiveStar GaugeGroupI where
  star_involutive g := by
    ext1 <;> simp

/-- The inclusion of a U(1) subgroup. -/
def ofU1Subgroup (u1 : unitary ℂ) : GaugeGroupI :=
  (1,
  ⟨!![star (u1 ^ 3 : unitary ℂ), 0;0, (u1 ^ 3 : unitary ℂ)], by
    simp only [SetLike.mem_coe]
    rw [mem_unitaryGroup_iff']
    funext i j
    rw [Matrix.mul_apply]
    fin_cases i <;> fin_cases j <;> simp [conj_mul'], by
    simp only [RCLike.star_def, SetLike.mem_coe, MonoidHom.mem_mker, coe_detMonoidHom,
      det_fin_two_of, conj_mul', mul_zero, sub_zero]
    simp⟩, u1)

@[simp]
lemma ofU1Subgroup_toSU3 (u1 : unitary ℂ) :
    toSU3 (ofU1Subgroup u1) = 1 := rfl

@[simp]
lemma ofU1Subgroup_toSU2 (u1 : unitary ℂ) :
    toSU2 (ofU1Subgroup u1) = ⟨!![star (u1 ^ 3 : unitary ℂ), 0;0, (u1 ^ 3 : unitary ℂ)], by
    simp only [SetLike.mem_coe]
    rw [mem_unitaryGroup_iff']
    funext i j
    rw [Matrix.mul_apply]
    fin_cases i <;> fin_cases j <;> simp [conj_mul'], by
    simp only [RCLike.star_def, SetLike.mem_coe, MonoidHom.mem_mker, coe_detMonoidHom,
      det_fin_two_of, conj_mul', mul_zero, sub_zero]
    simp⟩ := rfl

@[simp]
lemma ofU1Subgroup_toU1 (u1 : unitary ℂ) :
    toU1 (ofU1Subgroup u1) = u1 := rfl
end GaugeGroupI

/-!

## The ℤ₆ subgroup

The ℤ₆-subgroup of the gauge group consists of elements `(α² • I₃, α⁻³ • I₂, α)` where `α` is a
sixth root of unity. We define the primitive sixth root `ζ₆ = exp(πi/3)` and use it to construct
the generator of this cyclic subgroup.

-/

/-- The primitive sixth root of unity `exp(πi/3)`. -/
noncomputable def ζ₆ : ℂ := exp (Real.pi * I / 3)

/-- `ζ₆` raised to the 6th power equals 1. -/
lemma ζ₆_pow_6 : ζ₆ ^ 6 = 1 := by
  simp only [ζ₆, ← exp_nat_mul]; ring_nf
  have : (Real.pi : ℂ) * I * 2 = 2 * Real.pi * I := by ring
  rw [this]; exact exp_two_pi_mul_I

/-- `ζ₆` satisfies `star ζ₆ * ζ₆ = 1`. -/
lemma ζ₆_star_mul_self : star ζ₆ * ζ₆ = 1 := by
  simp only [ζ₆, RCLike.star_def, ← exp_conj, ← exp_add]
  simp only [map_div₀, map_mul, conj_ofReal, conj_I, conj_ofNat]; ring_nf; simp

/-- `ζ₆` satisfies `ζ₆ * star ζ₆ = 1`. -/
lemma ζ₆_mul_star_self : ζ₆ * star ζ₆ = 1 := by rw [mul_comm]; exact ζ₆_star_mul_self

/-- `(ζ₆²)³ = 1`, showing `ζ₆²` is a cube root of unity. -/
lemma ζ₆_sq_cubed : (ζ₆^2) ^ 3 = 1 := by rw [← pow_mul]; norm_num; exact ζ₆_pow_6

/-- `ζ₆³ = -1`. -/
lemma ζ₆_pow_3 : ζ₆ ^ 3 = -1 := by
  simp only [ζ₆, ← exp_nat_mul]; ring_nf; exact exp_pi_mul_I

/-- `ζ₆` is in the unitary group. -/
lemma ζ₆_mem_unitary : ζ₆ ∈ unitary ℂ :=
  Unitary.mem_iff.mpr ⟨ζ₆_star_mul_self, ζ₆_mul_star_self⟩

/-- Helper lemma: a scalar matrix `ω • I` is in SU(3) if `ω` is unitary and `ω³ = 1`. -/
lemma scalar_mem_SU3 {ω : ℂ} (hω_unitary : star ω * ω = 1) (hω_det : ω^3 = 1) :
    ω • (1 : Matrix (Fin 3) (Fin 3) ℂ) ∈ specialUnitaryGroup (Fin 3) ℂ := by
  rw [mem_specialUnitaryGroup_iff]
  constructor
  · rw [mem_unitaryGroup_iff', star_smul, star_one, smul_mul_smul, mul_one, hω_unitary, one_smul]
  · rw [det_smul, det_one, mul_one, Fintype.card_fin, hω_det]

/-- Helper lemma: a scalar matrix `ω • I` is in SU(2) if `ω` is unitary and `ω² = 1`. -/
lemma scalar_mem_SU2 {ω : ℂ} (hω_unitary : star ω * ω = 1) (hω_det : ω^2 = 1) :
    ω • (1 : Matrix (Fin 2) (Fin 2) ℂ) ∈ specialUnitaryGroup (Fin 2) ℂ := by
  rw [mem_specialUnitaryGroup_iff]
  constructor
  · rw [mem_unitaryGroup_iff', star_smul, star_one, smul_mul_smul, mul_one, hω_unitary, one_smul]
  · rw [det_smul, det_one, mul_one, Fintype.card_fin, hω_det]

/-- `star (ζ₆²) * ζ₆² = 1`. -/
lemma ζ₆_sq_star_mul_self : star (ζ₆^2) * (ζ₆^2) = 1 := by
  simp only [star_pow, RCLike.star_def]
  have h1 : (starRingEnd ℂ) ζ₆ = star ζ₆ := rfl
  rw [h1]
  calc (star ζ₆)^2 * ζ₆^2 = (star ζ₆ * ζ₆)^2 := by ring
    _ = 1^2 := by rw [ζ₆_star_mul_self]
    _ = 1 := one_pow 2

/-- `ζ₆² • I₃` is in SU(3). -/
lemma ζ₆_sq_smul_one_mem_SU3 :
    (ζ₆^2) • (1 : Matrix (Fin 3) (Fin 3) ℂ) ∈ specialUnitaryGroup (Fin 3) ℂ :=
  scalar_mem_SU3 ζ₆_sq_star_mul_self ζ₆_sq_cubed

/-- `-1 • I₂` is in SU(2). -/
lemma neg_one_smul_one_mem_SU2 :
    (-1 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) ∈ specialUnitaryGroup (Fin 2) ℂ :=
  scalar_mem_SU2 (by simp) (by norm_num)

/-- The generator of the ℤ₆-subgroup of `GaugeGroupI`: `(ζ₆² • I₃, -I₂, ζ₆)`.
This corresponds to the element `(α², α⁻³, α)` for `α = ζ₆`, noting that `ζ₆⁻³ = ζ₆³ = -1`. -/
noncomputable def gaugeGroupℤ₆_generator : GaugeGroupI :=
  (⟨ζ₆^2 • 1, ζ₆_sq_smul_one_mem_SU3⟩,
   ⟨-1 • 1, neg_one_smul_one_mem_SU2⟩,
   ⟨ζ₆, ζ₆_mem_unitary⟩)

/-- The subgroup of the un-quotiented gauge group which acts trivially on all particles in the
standard model, i.e., the ℤ₆-subgroup of `GaugeGroupI` with elements `(α^2 * I₃, α^(-3) * I₂, α)`,
where `α` is a sixth complex root of unity. This is the cyclic subgroup generated by
`gaugeGroupℤ₆_generator`.

See https://math.ucr.edu/home/baez/guts.pdf
-/
noncomputable def gaugeGroupℤ₆SubGroup : Subgroup GaugeGroupI :=
  Subgroup.zpowers gaugeGroupℤ₆_generator

/-- The smallest possible gauge group of the Standard Model, i.e., the quotient of `GaugeGroupI` by
the ℤ₆-subgroup `gaugeGroupℤ₆SubGroup`.

See https://math.ucr.edu/home/baez/guts.pdf
-/
def GaugeGroupℤ₆ : Type := GaugeGroupI ⧸ gaugeGroupℤ₆SubGroup

/-- The ℤ₂subgroup of the un-quotiented gauge group which acts trivially on all particles in the
standard model, i.e., the ℤ₂-subgroup of `GaugeGroupI` derived from the ℤ₂ subgroup of
`gaugeGroupℤ₆SubGroup`.

See https://math.ucr.edu/home/baez/guts.pdf
-/
informal_definition gaugeGroupℤ₂SubGroup where
  deps := [``GaugeGroupI]
  tag := "6V2GH"

/-- The gauge group of the Standard Model with a ℤ₂ quotient, i.e., the quotient of `GaugeGroupI` by
the ℤ₂-subgroup `gaugeGroupℤ₂SubGroup`.

See https://math.ucr.edu/home/baez/guts.pdf
-/
informal_definition GaugeGroupℤ₂ where
  deps := [``GaugeGroupI, ``StandardModel.gaugeGroupℤ₂SubGroup]
  tag := "6V2GO"

/-- The ℤ₃-subgroup of the un-quotiented gauge group which acts trivially on all particles in the
standard model, i.e., the ℤ₃-subgroup of `GaugeGroupI` derived from the ℤ₃ subgroup of
`gaugeGroupℤ₆SubGroup`.

See https://math.ucr.edu/home/baez/guts.pdf
-/
informal_definition gaugeGroupℤ₃SubGroup where
  deps := [``GaugeGroupI]
  tag := "6V2GV"

/-- The gauge group of the Standard Model with a ℤ₃-quotient, i.e., the quotient of `GaugeGroupI` by
the ℤ₃-subgroup `gaugeGroupℤ₃SubGroup`.

See https://math.ucr.edu/home/baez/guts.pdf
-/
informal_definition GaugeGroupℤ₃ where
  deps := [``GaugeGroupI, ``StandardModel.gaugeGroupℤ₃SubGroup]
  tag := "6V2G3"

/-- Specifies the allowed quotients of `SU(3) x SU(2) x U(1)` which give a valid
  gauge group of the Standard Model. -/
inductive GaugeGroupQuot : Type
  /-- The element of `GaugeGroupQuot` corresponding to the quotient of the full SM gauge group
    by the sub-group `ℤ₆`. -/
  | ℤ₆ : GaugeGroupQuot
  /-- The element of `GaugeGroupQuot` corresponding to the quotient of the full SM gauge group
    by the sub-group `ℤ₂`. -/
  | ℤ₂ : GaugeGroupQuot
  /-- The element of `GaugeGroupQuot` corresponding to the quotient of the full SM gauge group
    by the sub-group `ℤ₃`. -/
  | ℤ₃ : GaugeGroupQuot
  /-- The element of `GaugeGroupQuot` corresponding to the full SM gauge group. -/
  | I : GaugeGroupQuot

/-- The (global) gauge group of the Standard Model given a choice of quotient, i.e., the map from
`GaugeGroupQuot` to `Type` which gives the gauge group of the Standard Model for a given choice of
quotient.

See https://math.ucr.edu/home/baez/guts.pdf
-/
informal_definition GaugeGroup where
  deps := [``GaugeGroupI, ``gaugeGroupℤ₂SubGroup, ``gaugeGroupℤ₃SubGroup,
    ``GaugeGroupQuot]
  tag := "6V2HF"

/-!

## Smoothness structure on the gauge group.

-/

/-- The gauge group `GaugeGroupI` is a Lie group. -/
informal_lemma gaugeGroupI_lie where
  deps := [``GaugeGroupI]
  tag := "6V2HL"

/-- For every `q` in `GaugeGroupQuot` the group `GaugeGroup q` is a Lie group. -/
informal_lemma gaugeGroup_lie where
  deps := [``GaugeGroup]
  tag := "6V2HR"

/-- The trivial principal bundle over SpaceTime with structure group `GaugeGroupI`. -/
informal_definition gaugeBundleI where
  deps := [``GaugeGroupI, ``SpaceTime]
  tag := "6V2HX"

/-- A global section of `gaugeBundleI`. -/
informal_definition gaugeTransformI where
  deps := [``gaugeBundleI]
  tag := "6V2H5"

end StandardModel
