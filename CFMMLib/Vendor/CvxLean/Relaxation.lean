/-!
# Relaxation of optimization problems

Vendored from: verified-optimization/CvxLean (CvxLean/Lib/Relaxation.lean)
Authors: Alexander Bentkamp, Ramon Fernández Mir, Jeremy Avigad
License: Apache 2.0
Adapted for Lean 4.28.0 / current Mathlib.

p ≽' q means: q is a relaxation of p (forward map, feasibility + bound).
-/

import CFMMLib.Vendor.CvxLean.Equivalence

set_option autoImplicit false

namespace Minimization

variable {D E F R : Type} [Preorder R]
variable (p : Minimization D R) (q : Minimization E R)

/-- `Relaxation p q`: q is a relaxation of p. -/
structure Relaxation where
  phi : D → E
  phi_feasibility : ∀ x, p.feasible x → q.feasible (phi x)
  phi_optimality : ∀ x, p.feasible x → q.objFun (phi x) ≤ p.objFun x

namespace Relaxation

variable {p q}

notation p " ≽' " q => Relaxation p q

def refl : p ≽' p :=
  { phi := id,
    phi_feasibility := fun _ h => h,
    phi_optimality := fun _ _ => le_refl _ }

/-- Removing a constraint is a relaxation. -/
def remove_constraint {f : D → R} {c cs' : D → Prop}
    (hcs : ∀ x, p.constraints x ↔ c x ∧ cs' x) :
    p ≽' ⟨f, cs'⟩ :=
  { phi := id,
    phi_feasibility := fun x h_feas_x => ((hcs x).mp h_feas_x).2,
    phi_optimality := fun _ _ => le_refl _ }

/-- Weakening constraints is a relaxation. -/
def weaken_constraints {f : D → R} (cs' : D → Prop)
    (hcs : ∀ x, p.constraints x → cs' x) :
    p ≽' ⟨f, cs'⟩ :=
  { phi := id,
    phi_feasibility := fun x h => hcs x h,
    phi_optimality := fun _ _ => le_refl _ }

end Relaxation

end Minimization
