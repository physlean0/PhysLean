/-
Copyright (c) 2025 PhysLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PhysLean Contributors
-/
import PhysLean.Relativity.Special.TwinParadox.Basic
import PhysLean.Meta.Informal.SemiFormal
/-!
# General Twin Paradox

## i. Overview

This module extends the twin paradox formalization to handle arbitrary worldlines,
not just the instantaneous acceleration case with three spacetime points.

The general twin paradox states:
**Among all future-directed timelike worldlines connecting two events in Minkowski
spacetime, the geodesic (straight line) has the maximum proper time.**

This is the relativistic "reverse triangle inequality" for paths: detours through
spacetime always result in less elapsed proper time, which is the physical basis
for time dilation and the twin paradox.

## ii. Key definitions

- `Worldline`: A smooth curve through spacetime
- `TimelikeWorldline`: A worldline whose tangent vector is always timelike
- `properTimeAlong`: The proper time elapsed along a worldline (as an integral)

## iii. Key results

- `general_twin_paradox`: The straight-line worldline maximizes proper time
  among all timelike worldlines connecting the same two events

## iv. Relationship to InstantaneousTwinParadox

The `InstantaneousTwinParadox` module proves the special case where twin B
travels along two straight-line segments. The general case here handles
arbitrary smooth worldlines, with the piecewise linear case as a limit.

## v. References

- Rindler, Introduction to Special Relativity, Chapter 3
- Misner, Thorne, Wheeler, Gravitation, Chapter 6

-/

noncomputable section

namespace SpecialRelativity

open Matrix
open Real
open Lorentz
open Vector
open MeasureTheory

variable {d : ℕ}

/-!

## A. Worldlines

A worldline is a smooth parametrized curve through spacetime. For the twin paradox,
we require the worldline to be timelike (tangent vector always timelike) and
future-directed (time component of tangent vector positive).

-/

/-- A worldline is a smooth curve `γ : ℝ → SpaceTime d` through spacetime,
    parametrized by some parameter (not necessarily proper time). -/
structure Worldline (d : ℕ := 3) where
  /-- The curve through spacetime. -/
  path : ℝ → SpaceTime d
  /-- The worldline is smooth (infinitely differentiable). -/
  smooth : ContDiff ℝ ⊤ path

namespace Worldline

variable (γ : Worldline d)

/-- The tangent vector to the worldline at parameter value `s`. -/
def tangent (s : ℝ) : SpaceTime d := deriv γ.path s

/-- A worldline is timelike if its tangent vector is timelike everywhere. -/
def IsTimelike (γ : Worldline d) : Prop :=
  ∀ s : ℝ, causalCharacter (γ.tangent s) = CausalCharacter.timeLike

/-- A worldline is future-directed if the time component of its tangent
    is positive everywhere. -/
def IsFutureDirected (γ : Worldline d) : Prop :=
  ∀ s : ℝ, 0 < (γ.tangent s) (Sum.inl 0)

/-- A worldline is causal if it is timelike and future-directed. -/
def IsCausal (γ : Worldline d) : Prop :=
  γ.IsTimelike ∧ γ.IsFutureDirected

/-- The Minkowski norm of the tangent vector at a point.
    For a timelike worldline, this is positive. -/
def tangentNormSq (s : ℝ) : ℝ := ⟪γ.tangent s, γ.tangent s⟫ₘ

/-- The proper time element `dτ = √(⟪γ'(s), γ'(s)⟫ₘ) ds` at parameter `s`.
    For timelike worldlines, this is the infinitesimal proper time. -/
def properTimeElement (s : ℝ) : ℝ := sqrt (γ.tangentNormSq s)

end Worldline

/-!

## B. Proper time along a worldline

The proper time along a worldline from parameter `a` to `b` is given by
the integral:

  τ = ∫_{a}^{b} √⟪γ'(s), γ'(s)⟫ₘ ds

For a straight-line worldline `γ(s) = p + s(q - p)` with `s ∈ [0, 1]`,
this gives `τ = √⟪q - p, q - p⟫ₘ`, which matches `SpaceTime.properTime`.

-/

/-- The proper time elapsed along a worldline segment from parameter `a` to `b`.

    For a timelike worldline, this is always non-negative and represents the
    physical elapsed time measured by a clock traveling along the worldline. -/
noncomputable def properTimeAlong (γ : Worldline d) (a b : ℝ) : ℝ :=
  ∫ s in Set.Icc a b, γ.properTimeElement s

/-- The straight-line worldline from spacetime point `p` to `q`. -/
def straightLineWorldline (p q : SpaceTime d) : Worldline d where
  path := fun s => p + s • (q - p)
  smooth := by
    apply ContDiff.add
    · exact contDiff_const
    · exact ContDiff.smul contDiff_id contDiff_const

namespace straightLineWorldline

variable (p q : SpaceTime d)

/-- The tangent vector of the straight-line worldline is constant and equal to `q - p`. -/
lemma tangent_eq (s : ℝ) : (straightLineWorldline p q).tangent s = q - p := by
  unfold Worldline.tangent straightLineWorldline
  simp only
  have h1 : (fun s : ℝ => p + s • (q - p)) = (fun s : ℝ => s • (q - p) + p) := by
    funext x
    exact add_comm _ _
  rw [h1]
  rw [deriv_add_const']
  rw [deriv_smul_const]
  · simp
  · exact differentiableAt_fun_id

/-- A straight-line worldline is timelike if and only if `q - p` is timelike. -/
lemma isTimelike_iff :
    Worldline.IsTimelike (straightLineWorldline p q) ↔
    causalCharacter (q - p) = CausalCharacter.timeLike := by
  unfold Worldline.IsTimelike
  simp only [tangent_eq]
  constructor
  · intro h
    exact h 0
  · intro h s
    exact h

/-- A straight-line worldline is future-directed if and only if
    the time component of `q - p` is positive. -/
lemma isFutureDirected_iff :
    Worldline.IsFutureDirected (straightLineWorldline p q) ↔
    0 < (q - p) (Sum.inl 0) := by
  unfold Worldline.IsFutureDirected
  simp only [tangent_eq]
  constructor
  · intro h
    exact h 0
  · intro h s
    exact h

/-- The tangent norm squared of a straight-line worldline is constant. -/
lemma tangentNormSq_eq (s : ℝ) :
    (straightLineWorldline p q).tangentNormSq s = ⟪q - p, q - p⟫ₘ := by
  unfold Worldline.tangentNormSq
  rw [tangent_eq]

/-- The proper time element of a straight-line worldline is constant. -/
lemma properTimeElement_eq (s : ℝ) :
    (straightLineWorldline p q).properTimeElement s = sqrt ⟪q - p, q - p⟫ₘ := by
  unfold Worldline.properTimeElement
  rw [tangentNormSq_eq]

/-- The straight-line worldline starts at `p` when `s = 0`. -/
lemma path_zero : (straightLineWorldline p q).path 0 = p := by
  simp [straightLineWorldline]

/-- The straight-line worldline ends at `q` when `s = 1`. -/
lemma path_one : (straightLineWorldline p q).path 1 = q := by
  simp [straightLineWorldline]

end straightLineWorldline

/-!

## C. The General Twin Paradox Theorem

The main theorem states that among all timelike worldlines connecting two events,
the straight-line (geodesic) worldline has the maximum proper time.

This is proved using the reverse triangle inequality for timelike vectors.
The key insight is that any deviation from the straight path can be decomposed
into infinitesimal deviations, each of which loses proper time by the reverse
triangle inequality.

-/

/-- Two worldlines connect the same events if they have the same endpoints. -/
def connectSameEvents (γ₁ γ₂ : Worldline d) (a₁ b₁ a₂ b₂ : ℝ) : Prop :=
  γ₁.path a₁ = γ₂.path a₂ ∧ γ₁.path b₁ = γ₂.path b₂

/-- **General Twin Paradox Theorem (Semi-formal)**

Among all causal (timelike, future-directed) worldlines connecting two events
`p` and `q`, the straight-line worldline maximizes proper time.

Physically: A clock traveling on any detour through spacetime will measure
less elapsed time than a clock traveling directly from `p` to `q`.

The proof idea:
1. Any worldline can be approximated by piecewise straight segments
2. Each "kink" in the path loses proper time by the reverse triangle inequality
3. In the limit, any curved path has less proper time than the straight path

The n-point case follows by induction from `threePoint_twin_paradox` and
`fourPoint_twin_paradox`.
-/
informal_lemma general_twin_paradox where
  deps := [`Worldline, `properTimeAlong, `straightLineWorldline,
           `Lorentz.Vector.reverse_triangle_ineq]
  tag := "7ROQ4"

/-- For a straight-line worldline from `p` to `q` over `[0, 1]`,
    the proper time equals `SpaceTime.properTime p q`. -/
lemma straightLine_properTimeAlong_eq (p q : SpaceTime d) :
    properTimeAlong (straightLineWorldline p q) 0 1 = SpaceTime.properTime p q := by
  unfold properTimeAlong SpaceTime.properTime
  -- The integrand is constant
  have h_const : Set.EqOn (fun s => (straightLineWorldline p q).properTimeElement s)
      (fun _ => sqrt ⟪q - p, q - p⟫ₘ) (Set.Icc 0 1) := by
    intro s _
    exact straightLineWorldline.properTimeElement_eq p q s
  -- Use that integral of constant c over [0,1] is c
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Icc h_const]
  rw [MeasureTheory.setIntegral_const]
  rw [Real.volume_real_Icc]
  simp only [sub_zero, max_eq_left (by norm_num : (0 : ℝ) ≤ 1), one_smul]

/-- **Twin Paradox Strict Inequality (Semi-formal)**

If a causal worldline is not a straight line (i.e., has some "kink" or curvature),
then its proper time is strictly less than the straight-line proper time.

This is the precise statement that "taking a detour through spacetime always
ages you less than staying home".
-/
informal_lemma general_twin_paradox_strict where
  deps := [`Worldline, `properTimeAlong, `straightLineWorldline,
           `general_twin_paradox]
  tag := "7ROQ6"

/-!

## D. Piecewise Linear Worldlines

To connect the general theory with `InstantaneousTwinParadox`, we define
piecewise linear worldlines and show they are a special case.

-/

/-- A piecewise linear worldline through a sequence of spacetime points.
    The list must have at least 2 points and consecutive points must be
    causally connected. -/
structure PiecewiseLinearWorldline (d : ℕ := 3) where
  /-- The sequence of spacetime points (vertices). -/
  points : List (SpaceTime d)
  /-- There are at least two points (start and end). -/
  nonempty : points.length ≥ 2

namespace PiecewiseLinearWorldline

variable (W : PiecewiseLinearWorldline d)

/-- The starting point of the worldline. -/
def startPoint : SpaceTime d := W.points.head (by
  have h := W.nonempty
  cases hp : W.points with
  | nil => simp [hp] at h
  | cons hd tl => simp)

/-- The ending point of the worldline. -/
def endPoint : SpaceTime d := W.points.getLast (by
  have h := W.nonempty
  cases hp : W.points with
  | nil => simp [hp] at h
  | cons hd tl => simp)

/-- The straight-line proper time from start to end. -/
def straightLineProperTime : ℝ :=
  SpaceTime.properTime W.startPoint W.endPoint

/-- The total proper time along the piecewise linear worldline,
    computed as the sum of proper times between consecutive points. -/
def totalProperTime : ℝ :=
  (W.points.zip W.points.tail).map (fun (p, q) => SpaceTime.properTime p q) |>.sum

/-- Construct a 3-point piecewise linear worldline from an InstantaneousTwinParadox. -/
def ofInstantaneousTwinParadox (T : InstantaneousTwinParadox) : PiecewiseLinearWorldline 3 where
  points := [T.startPoint, T.twinBMid, T.endPoint]
  nonempty := by simp

/-- A piecewise linear worldline is causally valid if for all indices i < j,
    `causallyFollows (points[i]) (points[j])`. This ensures all pairs of points
    are in proper causal order. -/
def IsCausal (W : PiecewiseLinearWorldline 3) : Prop :=
  ∀ i j : Fin W.points.length, i < j →
    causallyFollows (W.points.get i) (W.points.get j)

end PiecewiseLinearWorldline

/-- The instantaneous twin paradox corresponds to a 3-point piecewise linear worldline.
    The proper time of twin B equals the total proper time of the piecewise worldline. -/
theorem instantaneous_is_piecewise_linear (T : InstantaneousTwinParadox) :
    (PiecewiseLinearWorldline.ofInstantaneousTwinParadox T).totalProperTime =
    InstantaneousTwinParadox.properTimeTwinB T := by
  unfold PiecewiseLinearWorldline.ofInstantaneousTwinParadox
  unfold PiecewiseLinearWorldline.totalProperTime
  unfold InstantaneousTwinParadox.properTimeTwinB
  simp only [List.zip_cons_cons, List.tail_cons, List.zip_nil_right, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil]
  ring

/-- **Three-Point Twin Paradox**

For three spacetime points `p`, `m`, `q` where `m` causally follows `p`
and `q` causally follows `m`, the proper time along the two-segment path
(p → m → q) is at most the proper time along the direct path (p → q).

This is the formal statement of the twin paradox: Twin B who travels
from p to m to q ages less than (or equal to) Twin A who travels
directly from p to q.

This is proved by the already-formalized `InstantaneousTwinParadox.ageGap_nonneg`. -/
theorem threePoint_twin_paradox (p m q : SpaceTime 3)
    (hpq : causallyFollows p q)
    (hpm : causallyFollows p m)
    (hmq : causallyFollows m q) :
    SpaceTime.properTime p m + SpaceTime.properTime m q ≤ SpaceTime.properTime p q := by
  -- Construct an InstantaneousTwinParadox
  let T : InstantaneousTwinParadox := {
    startPoint := p
    endPoint := q
    twinBMid := m
    endPoint_causallyFollows_startPoint := hpq
    twinBMid_causallyFollows_startPoint := hpm
    endPoint_causallyFollows_twinBMid := hmq
  }
  -- Use that ageGap_nonneg says properTimeTwinA - properTimeTwinB ≥ 0
  have h := InstantaneousTwinParadox.ageGap_nonneg T
  unfold InstantaneousTwinParadox.ageGap at h
  unfold InstantaneousTwinParadox.properTimeTwinA at h
  unfold InstantaneousTwinParadox.properTimeTwinB at h
  linarith

/-- **Four-Point Twin Paradox**

Generalizes the three-point case to four points by applying the
three-point theorem twice. -/
theorem fourPoint_twin_paradox (p₀ p₁ p₂ p₃ : SpaceTime 3)
    (h01 : causallyFollows p₀ p₁)
    (h12 : causallyFollows p₁ p₂)
    (h23 : causallyFollows p₂ p₃)
    (h02 : causallyFollows p₀ p₂)
    (h03 : causallyFollows p₀ p₃)
    (_ : causallyFollows p₁ p₃) :
    SpaceTime.properTime p₀ p₁ + SpaceTime.properTime p₁ p₂ +
      SpaceTime.properTime p₂ p₃ ≤ SpaceTime.properTime p₀ p₃ := by
  -- First apply three-point to (p₀, p₁, p₂) and (p₀, p₂)
  have h1 := threePoint_twin_paradox p₀ p₁ p₂ h02 h01 h12
  -- Then apply three-point to (p₀, p₂, p₃) and (p₀, p₃)
  have h2 := threePoint_twin_paradox p₀ p₂ p₃ h03 h02 h23
  -- Combine
  calc SpaceTime.properTime p₀ p₁ + SpaceTime.properTime p₁ p₂ + SpaceTime.properTime p₂ p₃
      ≤ SpaceTime.properTime p₀ p₂ + SpaceTime.properTime p₂ p₃ := by linarith
    _ ≤ SpaceTime.properTime p₀ p₃ := h2

/-- **Five-Point Twin Paradox**

Generalizes to five points by applying the four-point theorem. -/
theorem fivePoint_twin_paradox (p₀ p₁ p₂ p₃ p₄ : SpaceTime 3)
    (h01 : causallyFollows p₀ p₁)
    (h12 : causallyFollows p₁ p₂)
    (h23 : causallyFollows p₂ p₃)
    (h34 : causallyFollows p₃ p₄)
    (h02 : causallyFollows p₀ p₂)
    (h03 : causallyFollows p₀ p₃)
    (h04 : causallyFollows p₀ p₄)
    (h13 : causallyFollows p₁ p₃)
    (_ : causallyFollows p₁ p₄)
    (_ : causallyFollows p₂ p₄) :
    SpaceTime.properTime p₀ p₁ + SpaceTime.properTime p₁ p₂ +
      SpaceTime.properTime p₂ p₃ + SpaceTime.properTime p₃ p₄ ≤
      SpaceTime.properTime p₀ p₄ := by
  -- Apply four-point to (p₀, p₁, p₂, p₃)
  have h1 := fourPoint_twin_paradox p₀ p₁ p₂ p₃ h01 h12 h23 h02 h03 h13
  -- Apply three-point to (p₀, p₃, p₄)
  have h2 := threePoint_twin_paradox p₀ p₃ p₄ h04 h03 h34
  -- Combine
  linarith

/-- **Piecewise Linear Twin Paradox for Three Points**

For a causally valid 3-point worldline, the total proper time is at most
the straight-line proper time. This is just a restatement of `threePoint_twin_paradox`
for the `PiecewiseLinearWorldline` structure. -/
theorem piecewise_linear_twin_paradox_three (p₀ p₁ p₂ : SpaceTime 3)
    (h01 : causallyFollows p₀ p₁) (h12 : causallyFollows p₁ p₂) (h02 : causallyFollows p₀ p₂) :
    let W : PiecewiseLinearWorldline 3 := ⟨[p₀, p₁, p₂], by simp⟩
    W.totalProperTime ≤ W.straightLineProperTime := by
  -- Unfold definitions and simplify
  simp only [PiecewiseLinearWorldline.totalProperTime,
    PiecewiseLinearWorldline.straightLineProperTime,
    PiecewiseLinearWorldline.startPoint, PiecewiseLinearWorldline.endPoint,
    List.tail_cons, List.zip_cons_cons, List.zip_nil_right, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, _root_.add_zero, List.head_cons,
    List.getLast_cons_cons, List.getLast_singleton]
  exact threePoint_twin_paradox p₀ p₁ p₂ h02 h01 h12

/-- **Piecewise Linear Twin Paradox (Semi-formal)**

For any causally valid piecewise linear worldline with arbitrarily many points,
the total proper time is at most the straight-line proper time from start to end.

This is the general form of the twin paradox: taking any detour through spacetime
(visiting intermediate points along a causal path) results in less or equal
elapsed proper time compared to traveling directly.

The proof requires induction on the number of points, using `threePoint_twin_paradox`
at each step. The base case is n=2 (trivial equality), and the inductive step
uses the three-point inequality to combine proper times.

**Proof sketch:**
For points p₀, p₁, ..., pₙ:
- By IH: τ(p₁, p₂) + ... + τ(pₙ₋₁, pₙ) ≤ τ(p₁, pₙ)
- By three-point: τ(p₀, p₁) + τ(p₁, pₙ) ≤ τ(p₀, pₙ)
- Combining: τ(p₀, p₁) + τ(p₁, p₂) + ... + τ(pₙ₋₁, pₙ) ≤ τ(p₀, pₙ)
-/
informal_lemma piecewise_linear_twin_paradox where
  deps := [`PiecewiseLinearWorldline,
           `PiecewiseLinearWorldline.straightLineProperTime,
           `PiecewiseLinearWorldline.IsCausal,
           `threePoint_twin_paradox, `fourPoint_twin_paradox,
           `piecewise_linear_twin_paradox_three]
  tag := "7ROQ7"

/-!

## E. Connection to InstantaneousTwinParadox

The `InstantaneousTwinParadox` structure corresponds to a piecewise linear
worldline with exactly 3 points: startPoint, twinBMid, endPoint.

The `ageGap_nonneg` theorem from that module is a special case of
`piecewise_linear_twin_paradox`. This connection is now formalized in
`instantaneous_is_piecewise_linear`.
-/

end SpecialRelativity

end
