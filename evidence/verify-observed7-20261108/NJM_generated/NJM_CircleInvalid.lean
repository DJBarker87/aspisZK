import NJM_CircleRoot
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJM_CircleInvalid
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NIX_DispatchCut

def inputs {Pointer H : Type} (template : Pre Pointer) (record : r1_wire.ValidatedRecord)
 (before : r1_wire.SemanticTranscript H) : Pre Pointer :=
 { template with
   framed := record.framed
   row := record.row
   state := before.state
   next := before.next_row
   newState := before.state
   newNext := before.next_row
   reply := .Ok template.oldSample
   count := 0 }

/-- Invalid-row native dispatch has no callee, keeps the exact original
transcript, and preserves every observed log/frame cell per the cut. -/
theorem source {Pointer H : Type} (D : aspis_core.Digest32 H) (template : Pre Pointer)
 (record : r1_wire.ValidatedRecord) (before : r1_wire.SemanticTranscript H)
 (notFirst : record.row≠25#u8) (notSecond : record.row≠26#u8)
 (post : Post Pointer)
 (certificate : cut (NJM_CircleNative.install (inputs template record before)) post) :
 PreparedHashCode.run (NJM_CircleCode.source D before record)=([],ok (post.result,before)) ∧
 post.transcriptState=before.state ∧ post.transcriptNext=before.next_row ∧
 post.count=0 ∧ post.frame=template.frame := by
 have invalid : valid record.row=false := by simp [valid,notFirst,notSecond]
 have assoc:=NJM_CircleNative.invalid (inputs template record before) post certificate invalid
 have emitted : PreparedHashCode.run (NJM_CircleCode.source D before record)=([],ok (.Err .InvalidRow,before)) := by
  unfold NJM_CircleCode.source NJM_CircleCode.dispatch
  split
  · rename_i h;exact False.elim (notFirst h)
  · rename_i h;exact False.elim (notSecond h)
  · rfl
 refine ⟨?_,assoc.2⟩
 rw [assoc.1]
 exact emitted

#print axioms source
end AspisR1.NJM_CircleInvalid
end
