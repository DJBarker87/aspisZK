import NKU_FineRead
import NKK_Invoke
set_option autoImplicit false
noncomputable section
namespace NKU_InputAt
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission
/-- Caller-state invariant; checkpoint backing and cursor are not independent
witnesses. Native instantiations are the literal4/16/32 windows only. -/
def At (s : NKU.State) (cursor : Nat) : Prop :=
 s.frame.checkpoint.val.length=1768 ∧ s.reader.bytes=s.frame.checkpoint ∧ s.reader.at.val=cursor
def Inside (bytes : Slice U8) : NJU_ResumeObserved.Event → Prop
 | .raw n r _ => r.bytes=bytes ∧ r.at.val+n.val≤bytes.val.length
 | .k r _ => r.bytes=bytes ∧ r.at.val+16≤bytes.val.length
 | .e r _ => r.bytes=bytes ∧ r.at.val+32≤bytes.val.length
 | _ => True
theorem bound (s : NKU.State) (cursor width : Nat) (h : At s cursor)
 (fits : cursor+width≤1768) : s.reader.at.val+width≤s.reader.bytes.val.length := by
 rw [h.2.1,h.1,h.2.2]
 exact fits
theorem initial (f : NKU.Frame) (size : f.checkpoint.val.length=1768) : At (NKU.initial f) 0 :=
 ⟨size,rfl,rfl⟩
#print axioms bound
#print axioms initial
end NKU_InputAt
