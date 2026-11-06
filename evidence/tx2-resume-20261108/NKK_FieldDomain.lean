import NKK_FieldFold
import NKK_ReadFrames
import NKK_Invoke
import NJZ_Readers
set_option autoImplicit false
noncomputable section
namespace NKK_FieldDomain
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission NKK_FieldFold

def width : Kind → Nat | .k=>16 | .e=>32

def span (kinds : List Kind) : Nat := (kinds.map width).sum

/-- Complete returning child result and full Reader frame on a bounded raw
window. Rust Err is included; no successful-decoder hypothesis is required. -/
theorem bounded (kind : Kind) (r : Reader)
 (bound : r.at.val+width kind≤r.bytes.val.length) :
 ∃ (reply : core.result.Result Value verifier.Error) (next : Reader),
 response (event kind r)=ok (reply,next) ∧ NKK_ReadFrames.Frame (width kind) r next := by
 cases kind with
 | k =>
  obtain ⟨b,next,cut,run⟩:=NJZ_Readers.k_source r bound
  rw [NJZ_Readers.k_reference] at run
  refine ⟨mapInner Value.k (NIL_Carriers.unInner NIL_Carriers.unK (NJC_ReaderResults.naturalK b)),next,?_,cut.2.2,cut.2.1⟩
  change mapOuter _ (NIL_FreshOps.readK r)=_
  rw [run]
  rfl
 | e =>
  obtain ⟨b,next,cut,run⟩:=NJZ_Readers.e_source r bound
  rw [NJZ_Readers.e_reference] at run
  refine ⟨mapInner Value.e (NIL_Carriers.unInner NIL_Carriers.unE (NJC_EReaderResults.naturalE b)),next,?_,cut.2.2,cut.2.1⟩
  change mapOuter _ (NIL_FreshOps.readE r)=_
  rw [run]
  rfl

def Inside (bytes : Slice U8) : NJU_ResumeObserved.Event → Prop
 | .k r _ => r.bytes=bytes ∧ r.at.val+16≤bytes.val.length
 | .e r _ => r.bytes=bytes ∧ r.at.val+32≤bytes.val.length
 | _ => False

/-- Every call of the mixed stage lies in the CLOSED Reader's SAME backing
window. The actual post-state is used to derive the next bound. -/
theorem inside (kinds : List Kind) (r : Reader) (bytes : Slice U8)
 (backing : r.bytes=bytes) (bound : r.at.val+span kinds≤bytes.val.length) :
 NKK_LogClauses.Holds (Inside bytes) (program kinds r) := by
 induction kinds generalizing r with
 | nil => exact NKK_LogClauses.pure _ _
 | cons kind kinds ih =>
  have firstBound : r.at.val+width kind≤r.bytes.val.length := by
   rw [backing]
   simp only [span,List.map_cons,List.sum_cons] at bound
   omega
  obtain ⟨reply,next,run,frame⟩:=bounded kind r firstBound
  have nextBacking : next.bytes=bytes := frame.1.trans backing
  have nextBound : next.at.val+span kinds≤bytes.val.length := by
   change next.at.val+(kinds.map width).sum≤bytes.val.length
   have cursor:=frame.2
   simp only [span,List.map_cons,List.sum_cons] at bound
   omega
  unfold program
  apply NKK_Invoke.bind
  · change NKK_LogClauses.Holds (Inside bytes)
     (NJU_Log.record (fun _=>event kind r) (response (event kind r)))
    apply NKK_LogClauses.record
    cases kind <;> exact ⟨backing,by simpa only [width,backing] using firstBound⟩
  · rintro ⟨value,last⟩ accepted
    have same:=Result.ok.inj (run.symm.trans accepted)
    have reader:=congrArg Prod.snd same
    dsimp only at reader
    rw [←reader]
    cases value with
    | Err err => exact NKK_LogClauses.pure _ _
    | Ok value =>
     apply NKK_LogClauses.bind
     · exact ih next nextBacking nextBound
     · intro result
       exact NKK_LogClauses.pure _ _

#print axioms bounded
#print axioms inside
end NKK_FieldDomain
