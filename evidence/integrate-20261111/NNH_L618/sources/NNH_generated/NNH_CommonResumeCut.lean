import NNH_AuthCodeOk
set_option autoImplicit false
noncomputable section
namespace NNH_CommonResumeCut
open Aeneas Aeneas.Std Result AspisR1 VTop_Stages

theorem source (wr rr : NP6_StdModel.Reservation) (merkle : NJJ_Common.Merkle)
 (finish : NJJ_Common.Finish) {H : Type} (d : aspis_core.digest.Digest32 H)
 (pub proof ck : Slice U8) (hash : H)
 (success : NJJ_Common.run wr rr merkle finish d pub proof ck hash none=.ok (.Ok ())) :
 ∃ p a,NJJ_Common.resume wr d ck proof pub .S2 hash=.ok (.Ok (p,a)) ∧ a.next=10#usize := by
 unfold NJJ_Common.run at success
 cases resume : NJJ_Common.resume wr d ck proof pub .S2 hash with
 | fail e => simp only [resume,bind_tc_fail] at success; cases success
 | div => simp only [resume,bind_tc_div] at success; cases success
 | ok reply => cases reply with
   | Err e => simp only [resume,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch] at success; cases success
   | Ok pair =>
    rcases pair with ⟨p,a⟩
    simp only [resume,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch] at success
    refine ⟨p,a,rfl,?_⟩
    cases guard : (a.next != NHT_Constants.compact.SPLIT) with
    | true => simp only [guard,if_true] at success; cases success
    | false =>
     have equal := bne_eq_false_iff_eq.mp guard
     simpa only [NHT_Constants.compact.SPLIT] using equal
#print axioms source
end NNH_CommonResumeCut
