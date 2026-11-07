import LIB_VArray
import NGO_CanonicalPort
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
 obtain ⟨start,d,window,ce,final,same,chunks,native,run,halt,bound,terminal,rest⟩ :=
  NGO_DecodeComposed.result N off record call framed
 rcases terminal with ⟨finished,_⟩ | ⟨index,live,error,_,failed,reply⟩
 · have full : decodeMain N record off = .ok (.Ok (decoderArrayToMain final.1)) := by
    simpa only [finished,decoderResultToMain] using run
   refine ⟨.Ok (decoderArrayToMain final.1),full,?_⟩
   exact decodeMain_success_members_canonical N record off _ full
 · have full : decodeMain N record off = .ok (.Err (decoderErrorToMain error)) := by
    simpa only [failed,decoderResultToMain] using run
   exact ⟨.Err (decoderErrorToMain error),full,True.intro⟩
#print axioms total
end LIB_VDecodeTotal
