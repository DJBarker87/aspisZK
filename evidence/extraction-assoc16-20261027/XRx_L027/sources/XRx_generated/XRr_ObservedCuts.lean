import XRr_ObservedReject
import XRk_ResultTools
open Aeneas Aeneas.Std Result XRn_Join_Release XRk_ResultTools
set_option autoImplicit false
namespace XRr_ObservedCuts
/-- Exact prefix/public/begin/finish witnesses from ONE accepted source call. -/
theorem source {H : Type} (D : aspis_core.digest.Digest32 H)
 (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (bytes : Slice U8) (hash : H) (obs : Option (verifier.Phase → Result Unit))
 (sem : r1_semantic.Verified H)
 (run : r1_semantic.verify_observed D pub bytes hash obs=ok (.Ok sem)) :
 ∃ (p : r1_wire.Prefix) (initial after : r1_wire.SemanticTranscript H)
   (challenges : aspis_core.state_only_prefix.r0.Challenges),
 r1_wire.Prefix.parse bytes=ok (.Ok p) ∧
 r1_semantic.public_transcript D pub hash p.c1_root=ok (.Ok initial) ∧
 r1_wire.begin D p initial=ok (.Ok challenges,after) ∧
 r1_semantic.verify_finish D pub p after challenges obs=ok (.Ok sem) := by
 unfold r1_semantic.verify_observed at run
 obtain ⟨r,hparse,run⟩ := bind_success _ _ _ run
 cases r with
 | Err e => cases run
 | Ok p =>
   simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
   obtain ⟨marked,_,run⟩ := bind_success _ _ _ run
   obtain ⟨r,hpublic,run⟩ := bind_success _ _ _ run
   cases r with
   | Err e => cases run
   | Ok initial =>
     simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
     obtain ⟨r,after,hbegin,run⟩ := pair_bind_success _ _ _ run
     cases r with
     | Err e => cases run
     | Ok challenges =>
       simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
       obtain ⟨marked,_,run⟩ := bind_success _ _ _ run
       exact ⟨p,initial,after,challenges,hparse,hpublic,hbegin,run⟩
#print axioms source
end XRr_ObservedCuts
