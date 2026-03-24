import CFMMLib.Vendor.CvxLean.Equivalence

set_option autoImplicit false

/-!
# Reduction of optimization problems

Vendored from: verified-optimization/CvxLean (CvxLean/Lib/Reduction.lean)
Authors: Alexander Bentkamp, Ramon Fernández Mir, Jeremy Avigad
License: Apache 2.0
Adapted for Lean 4.28.0 / current Mathlib.

p ≼ q means: solving q gives a solution to p (backward map only).
-/

namespace Minimization

variable {D E F R : Type} [Preorder R]
variable (p : Minimization D R) (q : Minimization E R) (r : Minimization F R)

/-- `Reduction p q`: p reduces to q. Solving q yields a solution to p. -/
structure Reduction where
  psi : E → D
  psi_optimality : ∀ x, q.optimal x → p.optimal (psi x)

namespace Reduction

variable {p q r}

notation p " ≼ " q => Reduction p q

def refl : p ≼ p :=
  { psi := id,
    psi_optimality := fun _ hy => hy }

def trans (R₁ : p ≼ q) (R₂ : q ≼ r) : p ≼ r :=
  { psi := R₁.psi ∘ R₂.psi,
    psi_optimality := fun x h => R₁.psi_optimality (R₂.psi x) (R₂.psi_optimality x h) }

def toBwd (R : p ≼ q) : Solution q → Solution p :=
  fun sol =>
    { point := R.psi sol.point,
      isOptimal := R.psi_optimality sol.point sol.isOptimal }

def ofEquivalence (E : p ≡ q) : p ≼ q :=
  { psi := E.psi,
    psi_optimality := E.psi_optimality }

end Reduction

end Minimization
