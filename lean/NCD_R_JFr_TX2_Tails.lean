-- Exact generic geometry definitions retained; fixture-only certificates excluded.
import RPu_JFr_TX2_TailRead
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFr_TX2_Tails
open Aeneas Aeneas.Std Result

def start (slot : Fin 4) (kind : Fin 3) : Nat :=
  if kind.val=0 then 120*slot.val+104 else 480+32*slot.val+16*(kind.val-1)
def offset (slot : Fin 4) (kind : Fin 3) : Usize := Usize.ofNat (start slot kind) (by
  have := slot.isLt;have := kind.isLt;unfold start;split <;> scalar_tac)
def stop (slot : Fin 4) (kind : Fin 3) : Usize := Usize.ofNat (start slot kind+16) (by
  have := slot.isLt;have := kind.isLt;unfold start;split <;> scalar_tac)


end AspisR1.JFr_TX2_Tails
