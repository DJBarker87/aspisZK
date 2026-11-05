import NGO_CanonicalPort
import NGX_PrefixGeometry
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.NIH_DecodeInstall
open AspisR1PublicPreparation.RawActualDecodeKMainAdapter

/-- The callee packet is installed on this record, with its complete Rust
result. Framing is the remaining producer fact, not a decoder success premise. -/
theorem ready (N off : Usize) (record : MainRecord)
 (call : NGO_CallerDomains.Call record.row.val N.val off.val)
 (framed : record.framed.val.length=5+NFU_PacketDomains.payloadSize record.row.val) :
 record.framed.val.length≤3717 ∧
 32*off.val+32*N.val≤record.framed.val.length-5 ∧
 ∃ reply, decodeMain N record off=ok reply := by
 have numbers:=NGO_CallerDomains.numeric record.row.val N.val off.val call
 have cap:=NFU_PacketDomains.payload_bound record.row.val
 obtain ⟨start,d,window,ce,final,same,chunks,native,run,rest⟩:=
   NGO_DecodeComposed.result N off record call framed
 refine ⟨by omega,by omega,?_⟩
 cases status : final.2 with
 | none =>
   refine ⟨.Ok (decoderArrayToMain final.1),?_⟩
   simpa only [status,decoderResultToMain] using run
 | some reply =>
   cases reply with
   | Ok out =>
     refine ⟨.Ok (decoderArrayToMain out),?_⟩
     simpa only [status,decoderResultToMain] using run
   | Err error =>
     refine ⟨.Err (decoderErrorToMain error),?_⟩
     simpa only [status,decoderResultToMain] using run

/-- Each actual claims write gets the original row25 token and its own offset. -/
theorem claims (record : MainRecord) (p off : Usize)
 (row : record.row.val=25) (live : p.val<3) (offset : off.val=p.val*29)
 (framed : record.framed.val.length=3717) :
 record.framed.val.length≤3717 ∧
 32*off.val+32*29≤record.framed.val.length-5 ∧
 ∃ reply, decodeMain 29#usize record off=ok reply := by
 apply ready 29#usize off record
 · rw [row,offset]
   exact NGO_CallerDomains.Call.claims p.val live
 · rw [row]
   exact framed

/-- The ten round call sites all fit without a successful polynomial premise. -/
theorem round (record : MainRecord) (r : Usize)
 (live : r.val<10) (row : record.row.val=15+r.val)
 (framed : record.framed.val.length=NGX_PrefixGeometry.width (15+r.val)) :
 record.framed.val.length≤3717 ∧
 32*0+32*28≤record.framed.val.length-5 ∧
 ∃ reply, decodeMain 28#usize record 0#usize=ok reply := by
 apply ready 28#usize 0#usize record
 · rw [row]
   exact NGO_CallerDomains.Call.round (15+r.val) (by omega) (by omega)
 · simpa only [row,NGX_PrefixGeometry.width] using framed

#print axioms ready
#print axioms claims
#print axioms round
end AspisR1.NIH_DecodeInstall
