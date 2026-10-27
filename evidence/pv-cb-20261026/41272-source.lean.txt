import R1Z.PV_CB_HornerCell
set_option autoImplicit false
namespace R1Z.PV_CB_HornerFiniteCells
open Aeneas Aeneas.Std Result ProverRwSuccessReverseRange PV_CB_HornerCell

def finite (step : Usize → Q → Result Q) : Nat → Usize → Q → Result Q
  | 0,_,value => ok value
  | fuel+1,e,value => do
    let out ← step (pred e) value
    finite step fuel (pred e) out

theorem source (coeff : Coeff) (p : Prepared) (fuel : Nat) (e : Usize) (shared : Q) :
    PV_CB_MaskHorner.finite coeff p fuel e shared =
      finite (cell coeff p) fuel e shared := by
  induction fuel generalizing e shared with
  | zero => rfl
  | succ fuel ih =>
    simp only [PV_CB_MaskHorner.finite,finite,cell,bind_assoc_eq]
    repeat' (apply (Aeneas.Std.bind_eq_iff _ _ _).mpr;intro value hvalue)
    exact ih (pred e) _
#print axioms source
end R1Z.PV_CB_HornerFiniteCells
