import XRz_ParseFold
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XRz_ParseAdvance
/-- One symbolic parser-driver step, with the recursive suffix opaque. This
replaces repeated whole27-stage normalization after L067's heartbeat timeout. -/
theorem source (bytes : Slice U8) (i n : Nat) (records : List (Slice U8)) (offset : Usize) :
 XRx_TryDriver.run (XRz_ParseFold.step bytes) i (n+1) (records,offset)=
 (do let r ← r1_wire.parse_record_at bytes (XRz_ParseFold.row i) offset
     match r with
     | .Err e => ok (.Err e)
     | .Ok p => XRx_TryDriver.run (XRz_ParseFold.step bytes) (i+1) n (records++[p.1],p.2)) := by
 rw [XRx_TryDriver.run]
 unfold XRz_ParseFold.step
 cases h : r1_wire.parse_record_at bytes (XRz_ParseFold.row i) offset with
 | fail e => rfl
 | div => rfl
 | ok r => cases r <;> rfl
#print axioms source
end XRz_ParseAdvance
