import AspisR1DecodeKFullSuccessCanonicality
import LPq_ReadPorts
import ClaimsUnrolledFinishAdapters
import NP6_ClaimsModel
set_option autoImplicit false
noncomputable section
namespace AspisR1.LPs_ClaimsDomain
open Aeneas Aeneas.Std Result ClaimsUnrolledFinish AspisR1ClaimPreparedBridge
open LPi_FieldValues

def RowCanonical (a : Array MainQM 29#usize) : Prop := ∀ j : Fin 29,
  canonQ (LPq_ReadPorts.backQ (toClaimQ (a.val[j.val]'(by have h:=a.property;change a.val.length=29 at h;omega))))


private theorem step_success {A : Type}
    (m : Result (core.result.Result A ParentError))
    (k : A → Result AspisR1ClaimsUnrolledParent.Status) (out : MainClaims)
    (success : toMainStatus (do
      let r ← m
      match r with
      | .Err e => ok (.Err e)
      | .Ok a => k a)=ok (.Ok out)) :
    ∃ a,m=ok (.Ok a) ∧ toMainStatus (k a)=ok (.Ok out) := by
  cases m with
  | fail e => cases success
  | div => cases success
  | ok r =>
    cases r with
    | Err e => cases success
    | Ok a => exact ⟨a,rfl,success⟩

theorem decoded (r : AspisR1ClaimsUnrolledParent.Record) (off : Usize)
    (row : Array ParentQM 29#usize)
    (call : sourceDecode 29#usize r off=ok (.Ok row)) :
    RowCanonical (toMainArray row) := by
  have port := congrArg toMainDecoded call
  rw [decode_exact] at port
  unfold AspisS1ExtractedRoundChildren.decodeMain at port
  cases h : AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.decode_k 29#usize
      (AspisS1ExtractedRoundChildren.recordToDecoder (toMainRecord r)) off with
  | fail e => simp only [h,AspisS1ExtractedRoundChildren.decoderResultToMain] at port;cases port
  | div => simp only [h,AspisS1ExtractedRoundChildren.decoderResultToMain] at port;cases port
  | ok result =>
    cases result with
    | Err e => simp only [h,AspisS1ExtractedRoundChildren.decoderResultToMain] at port;cases port
    | Ok values =>
      simp only [h,AspisS1ExtractedRoundChildren.decoderResultToMain] at port
      have same := core.result.Result.Ok.inj (Result.ok.inj port)
      have canonical := AspisR1DecodeKFullSuccessCanonicality.decode_k_success_canonical
        29#usize _ off values h
      intro j
      have cell := canonical j
      rw [←same]
      simpa only [AspisS1ExtractedRoundChildren.decoderArrayToMain,List.getElem_map,
        AspisS1ExtractedRoundChildren.decoderQMToMain,toClaimQ,LPq_ReadPorts.backQ,
        canonQ,canonC,LPi_CMProduct.Canon,AspisR1DecodeKCanonicalArrayInvariant.Canonical,
        AspisR1DecodeKFullV10.aspis_core.field.P,
        show (2147483647#u32).val=2147483647 from rfl,and_assoc] using cell

def third (r : AspisR1ClaimsUnrolledParent.Record) (a b : Array ParentQM 29#usize) :
    Result AspisR1ClaimsUnrolledParent.Status := do
  let c ← sourceDecode 29#usize r 58#usize
  match c with
  | .Err e => ok (.Err e)
  | .Ok c => ok (.Ok ⟨[a,b,c],by simp⟩)

def second (r : AspisR1ClaimsUnrolledParent.Record) (a : Array ParentQM 29#usize) :
    Result AspisR1ClaimsUnrolledParent.Status := do
  let b ← sourceDecode 29#usize r 29#usize
  match b with
  | .Err e => ok (.Err e)
  | .Ok b => third r a b

def first (r : AspisR1ClaimsUnrolledParent.Record) : Result AspisR1ClaimsUnrolledParent.Status := do
  let a ← sourceDecode 29#usize r 0#usize
  match a with
  | .Err e => ok (.Err e)
  | .Ok a => second r a

set_option pp.all true in
theorem claims (pre : MainPrefix) (out : MainClaims)
    (success : ClaimsUnrolledFinish.claims (NP6_StdModel.calls (.Ok ())) pre=ok (.Ok out)) :
    ∀ row ∈ out.val, RowCanonical row := by
  rw [claims_value] at success
  unfold reference at success
  rw [NP6_ClaimsModel.reference_normalized] at success
  unfold NP6_ClaimsModel.normalized at success
  dsimp only at success
  obtain ⟨r,record,success⟩ := step_success
    ((external (NP6_StdModel.calls (.Ok ()))).validated (fromMainPrefix pre) 25#u8)
    first out (by simpa only [first,second,third,external,AspisR1ClaimsUnrolledParent.decodeRows] using success)
  change toMainStatus (first r)=ok (.Ok out) at success
  obtain ⟨a,da,success⟩ := step_success (sourceDecode 29#usize r 0#usize) (second r) out (by simpa only [first,second,third,external,AspisR1ClaimsUnrolledParent.decodeRows] using success)
  obtain ⟨b,db,success⟩ := step_success (sourceDecode 29#usize r 29#usize) (third r a) out (by simpa only [first,second,third,external,AspisR1ClaimsUnrolledParent.decodeRows] using success)
  obtain ⟨c,dc,success⟩ := step_success (sourceDecode 29#usize r 58#usize)
    (fun c => ok (.Ok ⟨[a,b,c],by simp⟩)) out (by simpa only [first,second,third,external,AspisR1ClaimsUnrolledParent.decodeRows] using success)
  have same := core.result.Result.Ok.inj (Result.ok.inj success)
  subst out
  intro row member
  change row ∈ [toMainArray a,toMainArray b,toMainArray c] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl
  · exact decoded r 0#usize a da
  · exact decoded r 29#usize b db
  · exact decoded r 58#usize c dc

#print axioms step_success
#print axioms decoded
#print axioms claims
end AspisR1.LPs_ClaimsDomain
end
