import JFv_TranscriptSpecs
set_option autoImplicit false
namespace AspisR1.JFv_Begin
open Aeneas Aeneas.Std Result WP
open AspisR1PublicPreparation

theorem success {H : Type} (D : aspis_core.Digest32 H) (total : JFv_TranscriptTotal.Total D)
    (pre : r1_wire.Prefix) (t0 : r1_wire.SemanticTranscript H) (initial : t0.next_row.val=0) :
    ∃ challenges after,r1_wire.begin D pre t0=ok (.Ok challenges,after) ∧ after.next_row.val=15 := by
  have spec : r1_wire.begin D pre t0
      ⦃ result => ∃ challenges after,result=(.Ok challenges,after) ∧ after.next_row.val=15 ⦄ := by
    unfold r1_wire.begin
    iterate 32
      all_goals try step*
      all_goals simp_all only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
        core.ops.control_flow.ControlFlow.Continue.injEq,
        core.ops.control_flow.ControlFlow.Break.injEq,Result.ok.injEq,Prod.mk.injEq,
        core.result.Result.Ok.injEq]
    all_goals scalar_tac
  obtain ⟨result,call,challenges,after,eq,next⟩ := WP.spec_imp_exists spec
  exact ⟨challenges,after,by rw [eq] at call;exact call,next⟩

#print axioms success
end AspisR1.JFv_Begin
