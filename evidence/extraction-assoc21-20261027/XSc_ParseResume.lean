import XRz_ParseAdvance
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XSc_ParseResume
def run (bytes : Slice U8) (root : Array U8 32#usize) (i n : Nat)
 (s : XRz_ParseFold.State) : Result (core.result.Result r1_wire.Prefix r1_wire.Error) := do
 let r ← XRx_TryDriver.run (XRz_ParseFold.step bytes) i n s
 match r with
 | .Err e => ok (.Err e)
 | .Ok state => XRz_ParseFold.finish bytes root state
/-- One generic symbolic first-stop parser step; its suffix remains opaque. -/
theorem advance (bytes : Slice U8) (root : Array U8 32#usize) (i n : Nat)
 (records : List (Slice U8)) (offset : Usize) :
 run bytes root i (n+1) (records,offset)= (do
  let r ← r1_wire.parse_record_at bytes (XRz_ParseFold.row i) offset
  match r with
  | .Err e => ok (.Err e)
  | .Ok pair => run bytes root (i+1) n (records++[pair.1],pair.2)) := by
 unfold run
 rw [XRz_ParseAdvance.source]
 simp only [bind_assoc_eq]
 congr 1
 funext r
 cases r <;> rfl
#print axioms advance
end XSc_ParseResume
