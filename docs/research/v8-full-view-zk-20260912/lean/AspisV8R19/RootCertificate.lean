/- Stepwise certificate rules. Concrete stages are supplied separately so no
   declaration expands the branching root recurrence to depth 22. -/
import AspisV8R19.SourceResidualPolynomial
import Mathlib.Data.ZMod.Basic

namespace AspisR19.RootCertificate
open ResidualModel SourceResidualPolynomial
variable {F : Type*} [CommRing F]
noncomputable section

theorem root_step (half root : F) (roots : List F) (p next out : Fin 27 → F)
    (hstep : ∀ j, shift half 1 p j-root*p j=next j)
    (hrest : rootRun half roots next=out) :
    rootRun half (root::roots) p=out := by
  change rootRun half roots (fun j => shift half 1 p j-root*p j)=out
  rw [show (fun j => shift half 1 p j-root*p j)=next from funext hstep]
  exact hrest

theorem root_append (half : F) (xs ys : List F) (p : Fin 27 → F) :
    rootRun half (xs++ys) p=rootRun half ys (rootRun half xs p) := by
  induction xs generalizing p with
  | nil => rfl
  | cons x xs ih => exact ih _

theorem shift_step (half : F) (n : Nat) (p current next : Fin 27 → F)
    (hcurrent : shift half n p=current)
    (hstep : ∀ r, (∑ j : Fin 27, current j*xEntry half j.val r.val)=next r) :
    shift half (n+1) p=next := by
  funext r
  simp only [shift,hcurrent]
  exact hstep r

/- A data vector uses literal canonical natural residues, not another recursive
   arithmetic expression. ZMod needs no primality assumption for these checks. -/
abbrev M := ZMod 2147483647
def vector (v : List Nat) (j : Fin 27) : M := (v.getD j.val 0 : M)
def half : M := 1073741824

theorem one_cell_preflight :
    shift half 1 (vector [1]) (1:Fin 27)-(1:M)*vector [1] 1=1 := by
  decide

#print axioms root_step
#print axioms root_append
#print axioms shift_step
#print axioms one_cell_preflight
end
end AspisR19.RootCertificate
