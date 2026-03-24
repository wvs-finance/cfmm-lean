import CFMMLib.Vendor.CvxLean.Equivalence

set_option autoImplicit false

/-!
# Relaxation of optimization problems

Vendored from: verified-optimization/CvxLean (CvxLean/Lib/Relaxation.lean)
Authors: Alexander Bentkamp, Ramon Fernández Mir, Jeremy Avigad
License: Apache 2.0
Adapted for Lean 4.28.0 / current Mathlib.

p ≽' q means: q is a relaxation of p (forward map, feasibility + bound).
-/

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
def remove_constraint {cs cs' : D → Prop}
    (hcs : ∀ x, cs x → cs' x) :
    (⟨p.objFun, cs⟩ : Minimization D R) ≽' ⟨p.objFun, cs'⟩ :=
  { phi := id,
    phi_feasibility := fun x h => hcs x h,
    phi_optimality := fun _ _ => le_refl _ }

/-- Weakening constraints is a relaxation. -/
def weaken_constraints (cs' : D → Prop)
    (hcs : ∀ x, p.constraints x → cs' x) :
    p ≽' ⟨p.objFun, cs'⟩ :=
  { phi := id,
    phi_feasibility := fun x h => hcs x h,
    phi_optimality := fun _ _ => le_refl _ }

end Relaxation

end Minimization
