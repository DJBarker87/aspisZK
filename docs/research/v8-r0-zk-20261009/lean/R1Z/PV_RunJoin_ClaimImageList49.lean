import R1Z.PV_RunJoin_ClaimCellImage49
import R1Z.PV_RunJoin_ClaimEvaluationList49
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ClaimImageList49
open Aeneas Aeneas.Std ProverRwFull
open PV_RunJoin_ClaimThread48 (W)
def stream (cell : Nat → List UInt8) (start : Nat) : Nat → List UInt8
  | 0 => []
  | n+1 => cell start ++ stream cell (start+1) n

theorem complete (out : Nat → W) (cell : Nat → List UInt8)
    (image : ∀ l,l<29 → (PV_RunJoin_FlatBytes35.wire (out l)).val.map PV_RunJoin_WideImage43.byte=cell l)
    (start n : Nat) (bound : start+n≤29) :
    (PV_RunJoin_ClaimImage48.bytes (PV_RunJoin_OrderedList48.run out start n)).map PV_RunJoin_WideImage43.byte=
      stream cell start n := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih =>
    rw [PV_RunJoin_OrderedList48.run,PV_RunJoin_ClaimImage48.bytes,List.map_append,
      image start (by omega),ih (start+1) (by omega)]
    rfl
#print axioms stream
#print axioms complete
end R1Z.PV_RunJoin_ClaimImageList49
