import Mathlib.Data.NNReal.Basic

set_option autoImplicit false

/-!
# Swap Rate Functions

Vendored from: dpusceddu/lean4-amm (AMMLib/Transaction/Swap/Rate.lean)
Authors: Daniele Pusceddu, Massimo Bartoletti, Alberto Lluch-Lafuente
License: MIT
Adapted for Lean 4.28.0 / current Mathlib.

Original uses custom `ℝ>0` (PReal). We use `ℝ>0` from Mathlib (PosReal)
where available, or plain `ℝ` with positivity hypotheses.

A swap rate function `SX` maps (input, reserve_in, reserve_out) → rate,
where the output amount = input * rate.
-/

/-- A swap rate function: given input x, reserve_in r₀, reserve_out r₁,
    returns the exchange rate. Output amount = x * (sx x r₀ r₁). -/
abbrev SX := ℝ → ℝ → ℝ → ℝ

namespace SX

/-- The output never drains the pool: x * sx(x, r₀, r₁) < r₁ -/
def outputbound (sx : SX) : Prop :=
  ∀ (x r₀ r₁ : ℝ), 0 < x → 0 < r₀ → 0 < r₁ →
    x * (sx x r₀ r₁) < r₁

/-- Monotonicity: better input/reserves → better rate -/
def mono (sx : SX) : Prop :=
  ∀ (x r₀ r₁ x' r₀' r₁' : ℝ),
    0 < x → 0 < r₀ → 0 < r₁ → 0 < x' → 0 < r₀' → 0 < r₁' →
    x' ≤ x → r₀' ≤ r₀ → r₁' ≤ r₁ →
    sx x r₀ r₁ ≤ sx x' r₀' r₁'

/-- Strict monotonicity -/
def strictmono (sx : SX) : Prop :=
  ∀ (x r₀ r₁ x' r₀' r₁' : ℝ),
    0 < x → 0 < r₀ → 0 < r₁ → 0 < x' → 0 < r₀' → 0 < r₁' →
    x' ≤ x → r₀' ≤ r₀ → r₁ ≤ r₁' →
    (x' < x ∨ r₀' < r₀ ∨ r₁ < r₁' → sx x r₀ r₁ < sx x' r₀' r₁') ∧
    sx x r₀ r₁ ≤ sx x' r₀' r₁'

/-- Homogeneity: scaling all arguments preserves the rate -/
def homogeneous (sx : SX) : Prop :=
  ∀ (a x r₀ r₁ : ℝ), 0 < a → 0 < x → 0 < r₀ → 0 < r₁ →
    sx (a * x) (a * r₀) (a * r₁) = sx x r₀ r₁

/-- Additivity: splitting a trade into two sequential trades is equivalent -/
def additive (sx : SX) : Prop :=
  ∀ (x y r₀ r₁ : ℝ), 0 < x → 0 < y → 0 < r₀ → 0 < r₁ →
    x * (sx x r₀ r₁) < r₁ →
    sx (x + y) r₀ r₁ =
      (x * (sx x r₀ r₁) + y * (sx y (r₀ + x) (r₁ - x * (sx x r₀ r₁)))) / (x + y)

/-- Reversibility: swapping and swapping back returns to original state -/
def reversible (sx : SX) : Prop :=
  ∀ (x r₀ r₁ : ℝ), 0 < x → 0 < r₀ → 0 < r₁ →
    x * (sx x r₀ r₁) < r₁ →
    sx (x * (sx x r₀ r₁))
       (r₁ - x * (sx x r₀ r₁))
       (x + r₀)
    = 1 / (sx x r₀ r₁)

end SX
