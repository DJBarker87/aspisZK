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

theorem claims (pre : MainPrefix) (out : MainClaims)
    (success : ClaimsUnrolledFinish.claims (NP6_StdModel.calls (.Ok ())) pre=ok (.Ok out)) :
    ∀ row ∈ out.val, RowCanonical row := by
  rw [claims_value] at success
  unfold reference at success
  rw [NP6_ClaimsModel.reference_normalized] at success
  unfold NP6_ClaimsModel.normalized at success
  dsimp only at success
  cases record : (external (NP6_StdModel.calls (.Ok ()))).validated (fromMainPrefix pre) 25#u8 with
  | fail e =>
    simp only [record,bind_tc_fail,toMainStatus,reduceCtorEq] at success
  | div =>
    simp only [record,bind_tc_div,toMainStatus,reduceCtorEq] at success
  | ok result =>
    cases result with
    | Err e =>
      simp only [record,bind_tc_ok,toMainStatus] at success
      cases success
    | Ok r =>
      simp only [record,bind_tc_ok] at success
      change toMainStatus (AspisR1ClaimsUnrolledParent.decodeRows
        (external (NP6_StdModel.calls (.Ok ()))) r)=ok (.Ok out) at success
      unfold AspisR1ClaimsUnrolledParent.decodeRows external at success
      cases da : sourceDecode 29#usize r 0#usize with
      | fail e =>
        simp only [da,bind_tc_fail,toMainStatus,reduceCtorEq] at success
      | div =>
        simp only [da,bind_tc_div,toMainStatus,reduceCtorEq] at success
      | ok result =>
        cases result with
        | Err e =>
          simp only [da,bind_tc_ok,toMainStatus] at success
          cases success
        | Ok a =>
          simp only [da,bind_tc_ok] at success
          cases db : sourceDecode 29#usize r 29#usize with
          | fail e =>
            simp only [db,bind_tc_fail,toMainStatus,reduceCtorEq] at success
          | div =>
            simp only [db,bind_tc_div,toMainStatus,reduceCtorEq] at success
          | ok result =>
            cases result with
            | Err e =>
              simp only [db,bind_tc_ok,toMainStatus] at success
              cases success
            | Ok b =>
              simp only [db,bind_tc_ok] at success
              cases dc : sourceDecode 29#usize r 58#usize with
              | fail e =>
                simp only [dc,bind_tc_fail,toMainStatus,reduceCtorEq] at success
              | div =>
                simp only [dc,bind_tc_div,toMainStatus,reduceCtorEq] at success
              | ok result =>
                cases result with
                | Err e =>
                  simp only [dc,bind_tc_ok,toMainStatus] at success
                  cases success
                | Ok c =>
                  simp only [dc,bind_tc_ok] at success
                  have same := core.result.Result.Ok.inj (Result.ok.inj success)
                  subst out
                  intro row member
                  change row ∈ [toMainArray a,toMainArray b,toMainArray c] at member
                  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
                  rcases member with rfl|rfl|rfl
                  · exact decoded r 0#usize a da
                  · exact decoded r 29#usize b db
                  · exact decoded r 58#usize c dc

#print axioms decoded
#print axioms claims
end AspisR1.LPs_ClaimsDomain
end
