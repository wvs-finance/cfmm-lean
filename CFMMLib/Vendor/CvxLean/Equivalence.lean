import CFMMLib.Vendor.CvxLean.Minimization

set_option autoImplicit false

/-!
# Equivalence of optimization problems

Vendored from: verified-optimization/CvxLean (CvxLean/Lib/Equivalence.lean)
Authors: Alexander Bentkamp, Ramon Fernández Mir, Jeremy Avigad
License: Apache 2.0
Adapted for Lean 4.28.0 / current Mathlib.

Two problems are equivalent if there exist maps φ, ψ between their domains
that preserve optimality in both directions.

Also defines StrongEquivalence (preserves feasibility + bounds objective).
-/

namespace Minimization

variable {D E F R : Type} [Preorder R]
variable (p : Minimization D R) (q : Minimization E R) (r : Minimization F R)

/-- Two problems are equivalent if optimal solutions can be mapped back and forth. -/
structure Equivalence where
  phi : D → E
  psi : E → D
  phi_optimality : ∀ x, p.optimal x → q.optimal (phi x)
  psi_optimality : ∀ x, q.optimal x → p.optimal (psi x)

namespace Equivalence

variable {p q r}

notation p " ≡ " q => Equivalence p q

def refl : p ≡ p :=
  { phi := id, psi := id,
    phi_optimality := fun _ h => h,
    psi_optimality := fun _ h => h }

def symm (E : p ≡ q) : q ≡ p :=
  { phi := E.psi, psi := E.phi,
    phi_optimality := E.psi_optimality,
    psi_optimality := E.phi_optimality }

def trans (E₁ : p ≡ q) (E₂ : q ≡ r) : p ≡ r :=
  { phi := E₂.phi ∘ E₁.phi,
    psi := E₁.psi ∘ E₂.psi,
    phi_optimality := fun x h => E₂.phi_optimality _ (E₁.phi_optimality x h),
    psi_optimality := fun x h => E₁.psi_optimality _ (E₂.psi_optimality x h) }

instance : Trans (@Equivalence D E R _) (@Equivalence E F R _) (@Equivalence D F R _) :=
  { trans := Equivalence.trans }

/-- Map an equivalence to a backward map between solutions. -/
def toFwd (E : p ≡ q) : Solution p → Solution q :=
  fun sol =>
    { point := E.phi sol.point,
      isOptimal := E.phi_optimality sol.point sol.isOptimal }

def toBwd (E : p ≡ q) : Solution q → Solution p :=
  fun sol =>
    { point := E.psi sol.point,
      isOptimal := E.psi_optimality sol.point sol.isOptimal }

end Equivalence

/-- A stronger notion: preserves feasibility and bounds the objective. -/
structure StrongEquivalence where
  phi : D → E
  psi : E → D
  phi_feasibility : ∀ x, p.feasible x → q.feasible (phi x)
  psi_feasibility : ∀ x, q.feasible x → p.feasible (psi x)
  phi_optimality : ∀ x, p.feasible x → q.objFun (phi x) ≤ p.objFun x
  psi_optimality : ∀ x, q.feasible x → p.objFun (psi x) ≤ q.objFun x

namespace StrongEquivalence

variable {p q}

notation p " ≡' " q => StrongEquivalence p q

end StrongEquivalence

/-- A strong equivalence implies an equivalence. -/
def Equivalence.ofStrongEquivalence (SE : p ≡' q) : p ≡ q :=
  { phi := SE.phi,
    psi := SE.psi,
    phi_optimality := fun x ⟨hfx, hopt⟩ =>
      ⟨SE.phi_feasibility x hfx,
       fun y hfy =>
         calc q.objFun (SE.phi x)
             ≤ p.objFun x := SE.phi_optimality x hfx
           _ ≤ p.objFun (SE.psi y) := hopt _ (SE.psi_feasibility y hfy)
           _ ≤ q.objFun y := SE.psi_optimality y hfy⟩,
    psi_optimality := fun x ⟨hfx, hopt⟩ =>
      ⟨SE.psi_feasibility x hfx,
       fun y hfy =>
         calc p.objFun (SE.psi x)
             ≤ q.objFun x := SE.psi_optimality x hfx
           _ ≤ q.objFun (SE.phi y) := hopt _ (SE.phi_feasibility y hfy)
           _ ≤ p.objFun y := SE.phi_optimality y hfy⟩ }

end Minimization
