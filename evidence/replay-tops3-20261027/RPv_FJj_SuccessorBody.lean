import RPv_FJj_SuccessorCell
set_option autoImplicit false
namespace AspisR1.FJj_SuccessorBody
open Aeneas Aeneas.Std Result ControlFlow
open FJc_WeightQMBridge (SQ)
open FJj_SuccessorCell (Rev next)

theorem cont (z p : Array SQ 10#usize) (carry : SQ) (iter cursor : Rev) (i : Usize)
    (hn : next iter=ok (some i,cursor))
    (r : ControlFlow (Rev × Array SQ 10#usize × SQ) (Array SQ 10#usize))
    (run : FIn_WeightsExtract.state_only_prefix.state_only_statement_points_loop.body z iter p carry=ok r) :
    ∃ (out : Array SQ 10#usize) (carryOut : SQ),r=.cont (cursor,out,carryOut) := by
  unfold next at hn
  unfold FIn_WeightsExtract.state_only_prefix.state_only_statement_points_loop.body at run
  rw [hn] at run
  simp only [bind_tc_ok] at run
  obtain ⟨bit,hbit,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨bc,hbc,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨q,hq,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨q1,hq1,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨q2,hq2,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨out,hu,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  exact ⟨out,bc,(Result.ok.inj run).symm⟩
#print axioms cont
end AspisR1.FJj_SuccessorBody
