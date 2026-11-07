import LIB_VDecodeCanonical
set_option autoImplicit false
noncomputable section
namespace LIB_VDecodeTotal
open Aeneas Aeneas.Std LIB_VScalarCarriers
open AspisR1 AspisR1PublicPreparation.RawActualDecodeKMainAdapter
abbrev Good {N : Usize} (r : core.result.Result (Array RawQ N) MainError) : Prop :=
 match r with | .Ok a => LIB_VArray.Canonical a | .Err _ => True
/-- Rule B induction, followed by the SAME entry/array/error carrier maps. -/
theorem total (N off : Usize) (record : MainRecord)
 (call : NGO_CallerDomains.Call record.row.val N.val off.val)
 (framed : record.framed.val.length=5+NFU_PacketDomains.payloadSize record.row.val) :
 ∃ out,decodeMain N record off = .ok out ∧ Good out := by
 have numbers := NGO_CallerDomains.numeric record.row.val N.val off.val call
 let start : Usize := Usize.ofNat (32*off.val) (by scalar_tac)
 have startValue : start.val=32*off.val := rfl
 obtain ⟨d,row⟩ := NGO_CallerDomains.record_domain N off start (recordToDecoder record) call framed startValue
 obtain ⟨size,finish,payload,window,offset,length,addition,original,get,same⟩ := NGO_EntryFacts.construct d
 obtain ⟨final,trace,run⟩ := NGO_DecodeTotal.ready N off start size finish
  (recordToDecoder record) payload window row offset length addition original get d
 have full := congrArg (decoderResultToMain N) run
 have canonical := LIB_VDecodeCanonical.trace d _ _ _ trace (LIB_VDecodeCanonical.zero N)
 obtain ⟨halt,_,_,terminal,_⟩ := NGO_FirstError.suffix d _ _ _ trace rfl (by simp)
 rcases terminal with ⟨finished,_⟩ | ⟨index,live,error,_,failed,reply⟩
 · refine ⟨.Ok (decoderArrayToMain final.1),?_,LIB_VDecodeCanonical.array N final.1 canonical⟩
   simpa only [finished,decoderResultToMain] using full
 · refine ⟨.Err (decoderErrorToMain error),?_,True.intro⟩
   simpa only [failed,decoderResultToMain] using full
#print axioms total
end LIB_VDecodeTotal
