import Mathlib.Order.Bounds.Basic

set_option autoImplicit false

/-!
# Minimization and Solution

Vendored from: verified-optimization/CvxLean (CvxLean/Lib/Minimization.lean)
Authors: Alexander Bentkamp, Ramon Fernández Mir, Jeremy Avigad
License: Apache 2.0
Adapted for Lean 4.28.0 / current Mathlib.

These are the building blocks: `Minimization` (optimization problems)
and `Solution` (optimal points).
-/

/-- Type of an optimization problem. -/
structure Minimization (D R : Type) where
  objFun : D → R
  constraints : D → Prop

namespace Minimization

variable {D E R : Type} [Preorder R]
variable (p : Minimization D R) (q : Minimization E R)

/-- A point `x : D` is feasible in `p` if it satisfies the constraints. -/
@[reducible]
def feasible (x : D) : Prop := p.constraints x

/-- A point `x : D` is optimal in `p` if it is feasible and for any feasible point `y : D` the
value of `x` is a lower bound to the value of `y`. -/
@[reducible]
def optimal (x : D) : Prop := p.feasible x ∧ ∀ y, p.feasible y → p.objFun x ≤ p.objFun y

/-- A solution is simply an optimal point. -/
structure Solution where
  point : D
  isOptimal : p.optimal point

end Minimization
