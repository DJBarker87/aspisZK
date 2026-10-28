import NCE_OpeningRead

set_option autoImplicit false
namespace AspisR1.NCE_OpeningCuts
open Aeneas Aeneas.Std Result MultiproofConeRef

/-- Source-order read continuation; only one byte is a native obligation.
Subsequent reads consume the actual preceding returned caller carrier. -/
def readWindow (reader : Reader) (i : Nat) : Nat → Nat → Carrier → Result (List U8 × Carrier)
  | 0,_,s => ok ([],s)
  | width+1,offset,s => do
      let first ← reader s (10055+832*i+offset)
      let rest ← readWindow reader i width (offset+1) first.2
      ok (first.1::rest.1,rest.2)

/-- A source-specific continuation proof from the one-byte native cut. The
full opening image is a conclusion and all nonproof caller fields are framed. -/
theorem read_window (reader : Reader) (cut : NCE_Native_Opening reader)
    (s : Carrier) (i width offset : Nat) (size : s.proof.val.length = 57607)
    (ib : i < 22) (span : offset+width ≤ 832) :
    readWindow reader i width offset s =
      ok (NBJ_WindowCover.image (fun k => s.proof.val[10055+832*i+k]!) offset width,s) := by
  induction width generalizing offset s with
  | zero => simp only [readWindow,NBJ_WindowCover.image,List.ofFn_zero]
  | succ width ih =>
    simp only [readWindow,read_byte reader cut s i offset size ib (by omega),
      bind_tc_ok,ih s (offset+1) size (by omega)]
    congr 1
    congr 1
    simp only [NBJ_WindowCover.image,List.ofFn_succ,Fin.val_zero,Fin.val_succ,
      Nat.zero_add,Nat.add_zero,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

/-- Full selected opening from the SAME immutable proof and caller carrier.
The raw native load/reborrow association is still the named one-byte cut. -/
theorem opening (reader : Reader) (cut : NCE_Native_Opening reader)
    (s : Carrier) (i : Nat) (size : s.proof.val.length = 57607) (ib : i < 22) :
    readWindow reader i 832 0 s =
      ok (NBJ_WindowCover.image (fun k => s.proof.val[k]!) (10055+832*i) 832,s) := by
  rw [read_window reader cut s i 832 0 size ib (by omega)]
  rw [NBJ_WindowCover.relocation]

#print axioms read_window
#print axioms opening
end AspisR1.NCE_OpeningCuts
