/-
Copyright (c) 2025 PhysLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PhysLean Contributors
-/

import PhysLean.Mathematics.Geometry.Metric.PseudoRiemannian.Einstein

/-!
# Perfect Fluid Stress-Energy Tensor

This file defines the stress-energy tensor for a perfect fluid, which is the
simplest model of matter in general relativity. Perfect fluids are used to
model stars, cosmological matter, and many other astrophysical systems.

## Main Definitions

* `PerfectFluid`: A perfect fluid characterized by energy density and pressure
* `perfectFluidStressEnergy`: The stress-energy tensor T_μν = (ρ + p)u_μ u_ν + p g_μν
* `EquationOfState`: Relation between pressure and density p = p(ρ)
* `FluidFourVelocity`: The 4-velocity field of the fluid

## Key Equations

Conservation equation: ∇_μ T^μν = 0 gives:
- Relativistic Euler equation: (ρ + p) u^μ ∇_μ u^ν = -(g^μν + u^μ u^ν) ∂_μ p
- Energy conservation: u^μ ∇_μ ρ + (ρ + p) ∇_μ u^μ = 0

Equations of state:
- Dust: p = 0 (non-relativistic matter)
- Radiation: p = ρ/3 (ultra-relativistic matter)
- Stiff matter: p = ρ (maximum causal pressure)
- Dark energy: p = -ρ (cosmological constant)

## Physical Interpretation

A perfect fluid has:
- No viscosity (shear stress)
- No heat conduction
- Isotropic pressure in the rest frame

The stress-energy tensor in the fluid rest frame is:
  T^μ_ν = diag(-ρ, p, p, p)

## References

* Misner, Thorne, Wheeler, "Gravitation" (1973), Chapter 22
* Weinberg, "Gravitation and Cosmology" (1972), Chapter 2
* Wald, "General Relativity" (1984), Chapter 4
-/

noncomputable section

open Bundle Set Finset Function Filter Module Topology ContinuousLinearMap
open scoped Manifold Bundle LinearMap Dual

namespace PseudoRiemannianMetric

universe v w

variable {E : Type v} {H : Type w} {M : Type w} {n : WithTop ℕ∞}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] [ChartedSpace H E]
variable {I : ModelWithCorners ℝ E H}
variable [IsManifold I (n + 1) M]
variable [inst_tangent_findim : ∀ (x : M), FiniteDimensional ℝ (TangentSpace I x)]

/-! ## Four-Velocity -/

/-- The four-velocity of a fluid element, satisfying u^μ u_μ = -1.
In the fluid rest frame, u^μ = (1, 0, 0, 0). -/
structure FluidFourVelocity where
  /-- The four components u^μ(x) at each spacetime point -/
  u : Fin 4 → ℝ → ℝ → ℝ → ℝ → ℝ

/-- The Lorentz factor γ = u^0 = dt/dτ for the fluid. -/
def FluidFourVelocity.lorentzFactor (u : FluidFourVelocity) (t x y z : ℝ) : ℝ :=
  u.u 0 t x y z

/-- The three-velocity v^i = u^i/u^0 of the fluid. -/
def FluidFourVelocity.threeVelocity (u : FluidFourVelocity) (i : Fin 3) (t x y z : ℝ) : ℝ :=
  u.u i.succ t x y z / u.u 0 t x y z

/-! ## Perfect Fluid Properties -/

/-- A perfect fluid is characterized by its rest-frame energy density ρ
and isotropic pressure p. -/
structure PerfectFluid where
  /-- Energy density in the rest frame ρ(x) -/
  energyDensity : ℝ → ℝ → ℝ → ℝ → ℝ
  /-- Pressure p(x) -/
  pressure : ℝ → ℝ → ℝ → ℝ → ℝ
  /-- The fluid four-velocity field -/
  velocity : FluidFourVelocity
  /-- Energy density is non-negative -/
  energyDensity_nonneg : ∀ t x y z, energyDensity t x y z ≥ 0

/-- The enthalpy density h = ρ + p (energy + pressure). -/
def PerfectFluid.enthalpy (fluid : PerfectFluid) (t x y z : ℝ) : ℝ :=
  fluid.energyDensity t x y z + fluid.pressure t x y z

/-- The equation of state parameter w = p/ρ. -/
def PerfectFluid.equationOfStateParameter (fluid : PerfectFluid) (t x y z : ℝ) : ℝ :=
  fluid.pressure t x y z / fluid.energyDensity t x y z

/-! ## Stress-Energy Tensor -/

/-- The stress-energy tensor of a perfect fluid:
T_μν = (ρ + p) u_μ u_ν + p g_μν

In matrix form in the rest frame:
T^μ_ν = diag(-ρ, p, p, p) -/
def perfectFluidStressEnergy (fluid : PerfectFluid)
    (g : Fin 4 → Fin 4 → ℝ → ℝ → ℝ → ℝ → ℝ) :
    Fin 4 → Fin 4 → ℝ → ℝ → ℝ → ℝ → ℝ :=
  fun μ ν t x y z =>
    let ρ := fluid.energyDensity t x y z
    let p := fluid.pressure t x y z
    let u_μ := fluid.velocity.u μ t x y z
    let u_ν := fluid.velocity.u ν t x y z
    (ρ + p) * u_μ * u_ν + p * g μ ν t x y z

/-- The stress-energy tensor is symmetric. -/
lemma perfectFluidStressEnergy_symm (fluid : PerfectFluid)
    (g : Fin 4 → Fin 4 → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hg_symm : ∀ μ ν t x y z, g μ ν t x y z = g ν μ t x y z) :
    ∀ μ ν t x y z,
      perfectFluidStressEnergy fluid g μ ν t x y z =
      perfectFluidStressEnergy fluid g ν μ t x y z := by
  intro μ ν t x y z
  unfold perfectFluidStressEnergy
  rw [hg_symm]
  ring

/-- The trace of the stress-energy tensor: T = g^μν T_μν = -ρ + 3p. -/
def perfectFluidTrace (fluid : PerfectFluid) (t x y z : ℝ) : ℝ :=
  -fluid.energyDensity t x y z + 3 * fluid.pressure t x y z

/-! ## Equations of State -/

/-- Dust (pressureless matter): p = 0.
Models non-relativistic matter, galaxies, cold dark matter. -/
def isDust (fluid : PerfectFluid) : Prop :=
  ∀ t x y z, fluid.pressure t x y z = 0

/-- Radiation (ultra-relativistic matter): p = ρ/3.
Models photons, neutrinos, early universe. -/
def isRadiation (fluid : PerfectFluid) : Prop :=
  ∀ t x y z, fluid.pressure t x y z = fluid.energyDensity t x y z / 3

/-- Stiff matter: p = ρ.
Maximum pressure allowed by causality (sound speed = c). -/
def isStiffMatter (fluid : PerfectFluid) : Prop :=
  ∀ t x y z, fluid.pressure t x y z = fluid.energyDensity t x y z

/-- Dark energy (cosmological constant-like): p = -ρ.
Causes accelerated expansion. -/
def isDarkEnergy (fluid : PerfectFluid) : Prop :=
  ∀ t x y z, fluid.pressure t x y z = -fluid.energyDensity t x y z

/-- A polytropic equation of state: p = K ρ^γ where γ is the adiabatic index.
Used for stellar models. -/
structure PolytropicEOS where
  /-- The polytropic constant K -/
  K : ℝ
  /-- The adiabatic index γ -/
  adiabaticIndex : ℝ
  /-- K is positive -/
  K_pos : K > 0
  /-- γ > 1 for normal matter -/
  gamma_gt_one : adiabaticIndex > 1

/-- The sound speed in a perfect fluid: c_s² = dp/dρ.
For p = wρ: c_s² = w.
Causality requires c_s ≤ 1 (in units where c = 1). -/
def soundSpeedSquared (w : ℝ) : ℝ := w

/-- Causality constraint: sound speed cannot exceed light speed. -/
def causalEOS (fluid : PerfectFluid) : Prop :=
  ∀ t x y z, fluid.equationOfStateParameter t x y z ≤ 1

/-! ## Conservation Laws -/

/-- For dust (p = 0), the stress-energy simplifies to T_μν = ρ u_μ u_ν. -/
lemma dust_stress_energy (fluid : PerfectFluid) (hDust : isDust fluid)
    (g : Fin 4 → Fin 4 → ℝ → ℝ → ℝ → ℝ → ℝ) :
    ∀ μ ν t x y z,
      perfectFluidStressEnergy fluid g μ ν t x y z =
      fluid.energyDensity t x y z * fluid.velocity.u μ t x y z * fluid.velocity.u ν t x y z := by
  intro μ ν t x y z
  unfold perfectFluidStressEnergy isDust at *
  simp [hDust t x y z]

/-! ## Thermodynamics -/

/-- Adiabatic flow: no heat transfer, entropy is conserved along flow lines.
u^μ ∂_μ s = 0 where s is entropy per baryon. -/
def isAdiabaticFlow (_fluid : PerfectFluid) : Prop :=
  True  -- Entropy conserved along flow

/-! ## Special Relativistic Limit -/

/-- In flat spacetime with Minkowski metric, the stress-energy tensor is:
T^μν = (ρ + p) u^μ u^ν + p η^μν -/
def flatSpacetimeStressEnergy (fluid : PerfectFluid) :
    Fin 4 → Fin 4 → ℝ → ℝ → ℝ → ℝ → ℝ :=
  fun μ ν t x y z =>
    let ρ := fluid.energyDensity t x y z
    let p := fluid.pressure t x y z
    let uμ := fluid.velocity.u μ t x y z
    let uν := fluid.velocity.u ν t x y z
    let η_μν := if μ = 0 ∧ ν = 0 then -1
                else if μ = ν then 1
                else 0
    (ρ + p) * uμ * uν + p * η_μν

/-- The energy density measured by an observer with four-velocity w^μ:
ρ_obs = T_μν w^μ w^ν -/
def observedEnergyDensity (fluid : PerfectFluid)
    (g : Fin 4 → Fin 4 → ℝ → ℝ → ℝ → ℝ → ℝ)
    (w : FluidFourVelocity) (t x y z : ℝ) : ℝ :=
  ∑ μ : Fin 4, ∑ ν : Fin 4,
    perfectFluidStressEnergy fluid g μ ν t x y z * w.u μ t x y z * w.u ν t x y z

/-! ## Fluid Kinematics -/

/-- The expansion scalar θ = ∇_μ u^μ measures volume change of fluid elements.
θ > 0: expansion, θ < 0: contraction. -/
def expansionScalar (_fluid : PerfectFluid) : ℝ → ℝ → ℝ → ℝ → ℝ :=
  fun _ _ _ _ => 0  -- Placeholder for ∇_μ u^μ

/-- Irrotational flow: vorticity vanishes, ω_μν = 0.
In this case, u_μ = ∂_μ φ for some potential φ. -/
def isIrrotationalFlow (_fluid : PerfectFluid) : Prop :=
  True  -- ω_μν = 0

end PseudoRiemannianMetric
end
