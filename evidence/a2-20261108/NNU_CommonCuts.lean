import NNU_Inactive
import NNU_Geometry
import NNU_Query
import NNU_Offsets
import NNH_CommonResumeDomain
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNU_CommonCuts
open Aeneas Aeneas.Std Result VTop_Stages

theorem source (env : RSL.Env) (pub proof ck : Slice U8)
 (success : LIBB_Tx2EnvCode.common env pub proof ck=.ok (.Ok ())) :
 ∃ p a g inactiveBytes decoded inactiveValue folded geo pending after afterPending,
 NJJ_Common.resume (LIBB_Tx2Reservation.reservation env) (LIBB_PartitionEnv.digest env)
   ck proof pub .S2 ()=.ok (.Ok (p,a)) ∧
 NHT_PacketOps.powers 29#usize p.gamma=.ok g ∧
 core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8) proof
   {start:=7495#usize,«end»:=7527#usize}=.ok inactiveBytes ∧
 NJC_ClosedCalls.inactive inactiveBytes=.ok decoded ∧
 NHT_Constants.core.option.Option.ok_or decoded AdapterRw.aspis_r1_cost_probe.verifier.Error.Parse=.ok (.Ok inactiveValue) ∧
 NLP_NativeMerkle.action (LIBB_PartitionEnv.H env) (LIBB_PartitionEnv.digest env)
   proof p folded 1#usize ()=.ok (.Ok ()) ∧
 NJC_ClosedCalls.geometry p.queries a.next 22#usize=.ok (.Ok geo) ∧
 NJJ_Common.pending (LIBB_Tx2Reservation.reservation env) a.weights.deref=.ok (.Ok pending) ∧
 NJJ_Common.query proof p a g none geo pending 22#usize=.ok (.Ok (after,afterPending)) := by
 unfold LIBB_Tx2EnvCode.common NJJ_Common.run at success
 rw [NNU_Offsets.inactive,NNU_Offsets.round0,NNU_Offsets.folded,NNU_Offsets.round1] at success
 repeat' first
 | (solve | cases success)
 | uncase_result
 | head_reduce success
 | split at success
 all_goals exact ⟨_,_,_,_,_,_,_,_,_,_,_,by assumption,by assumption,by assumption,
  by assumption,
  by assumption,by assumption,by assumption,by assumption,by assumption⟩
#print axioms source
end AspisR1.NNU_CommonCuts
end
