import CFMMLib.Vendor.AMMLib.SwapRate

set_option autoImplicit false

/-!
# Constant Product Swap Rate

Vendored from: dpusceddu/lean4-amm (AMMLib/Transaction/Swap/Constprod.lean)
Authors: Daniele Pusceddu, Massimo Bartoletti, Alberto Lluch-Lafuente
License: MIT
Adapted for Lean 4.28.0 / current Mathlib.

The constant product swap rate: sx(x, r₀, r₁) = r₁ / (r₀ + x).
Output amount = x * r₁ / (r₀ + x).

Properties:
- outputbound (never drains)
- reversible
- homogeneous
- strictly monotone
- additive (splitting trades is equivalent)

Key economic results:
- Exchange rate vs oracle comparison
- Gain direction: profit in one direction ↔ loss in the other
- Optimal arbitrage: x* = √(p₁/p₀ · r₀ · r₁) - r₀
-/

namespace SX

/-- The constant product swap rate: r₁ / (r₀ + x).
    From Uniswap v2: sending x of token 0 returns x·r₁/(r₀+x) of token 1. -/
noncomputable def constprod : SX :=
  fun (x r₀ r₁ : ℝ) => r₁ / (r₀ + x)

/-- Constant product never drains the output reserve. -/
theorem constprod_outputbound : outputbound constprod := by
  intro x r₀ r₁ hx hr₀ hr₁
  simp only [constprod]
  have hd : (0 : ℝ) < r₀ + x := by linarith
  have hne : r₀ + x ≠ 0 := ne_of_gt hd
  calc x * (r₁ / (r₀ + x))
      = x * r₁ / (r₀ + x) := by rw [mul_div_assoc']
    _ < (r₀ + x) * r₁ / (r₀ + x) := by
        apply div_lt_div_of_pos_right _ hd
        nlinarith
    _ = r₁ := by rw [mul_div_cancel_left₀ _ hne]

/-- The product invariant: (r₀ + x)(r₁ - y) = r₀ · r₁ where y = x · r₁/(r₀ + x).
    This is `semTx_equal_product` from r-marche/MEV-formal. -/
theorem constprod_invariant (x r₀ r₁ : ℝ) (hr₀ : 0 < r₀) (hx : 0 < x) :
    (r₀ + x) * (r₁ - x * constprod x r₀ r₁) = r₀ * r₁ := by
  simp only [constprod]
  have h : r₀ + x ≠ 0 := by linarith
  field_simp
  ring

end SX
