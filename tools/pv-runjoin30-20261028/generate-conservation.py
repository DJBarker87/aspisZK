from pathlib import Path
import sys
R=Path(__file__).resolve().parents[2];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
s='''import R1Z.PV_RunJoin_CheckedAddGuard30
import R1Z.PV_RunJoin_OuterBounds30
import R1Z.PV_RunJoin_Conservation29
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OuterConservation30
open Aeneas Aeneas.Std Result PV_RunJoin_Outer30
variable [LaneRoot] [R1Z.BuilderForestAdmissionPort.ExternalLinear] [R1Z.BuilderForestAdmissionPort.Records]
'''
for name,p,w,f in [('transfer','PoolV1PrivateTransferPublicV1','PoolV1PairForestPrivateTransferWitnessV1','compile_pool_v1_pair_forest_private_transfer_merged_c1_v1'),('withdrawal','PoolV1WithdrawalPublicV1','PoolV1PairForestWithdrawalWitnessV1','compile_pool_v1_pair_forest_withdrawal_merged_c1_v1')]:
 args='w.input.pair.value w.recipient.value w.change.value' if name=='transfer' else 'w.input.pair.value p.amount w.change.value'
 s+=f'''
theorem {name}
    (p : pool_v1.payment_relation.{p})
    (w : pool_v1.pair_forest_trace.{w})
    (context : pool_v1.payment_relation.PoolV1PaymentRelationContextV1)
    (snapshot : pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1)
    (c : pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (h : pool_v1.pair_forest_trace.{f} p w context snapshot = ok (.Ok c)) :
    PV_RunJoin_Conservation29.{name}Domain {args} := by
  unfold PV_RunJoin_Conservation29.{name}Domain
  unfold pool_v1.pair_forest_trace.{f} at h
  repeat' first
'''
 if name=='transfer':s+='''    | (refine ⟨PV_RunJoin_CheckedAddGuard30.positive _ (by assumption),
        PV_RunJoin_CheckedAddGuard30.positive _ (by assumption),
        PV_RunJoin_OuterBounds30.bound_of_guard _ (by assumption),
        PV_RunJoin_OuterBounds30.bound_of_guard _ (by assumption),?_⟩
       apply PV_RunJoin_CheckedAddGuard30.value <;> assumption)
'''
 else:s+='''    | (refine ⟨PV_RunJoin_CheckedAddGuard30.positive _ (by assumption),
        PV_RunJoin_OuterBounds30.bound_of_guard _ (by assumption),?_⟩
       apply PV_RunJoin_CheckedAddGuard30.value <;> assumption)
'''
 s+='''    | (have he : value = 1073741824#u32 := (Result.ok.inj hvalue).symm; subst value)
    | (pv_peel h with value hvalue)
    | exact False.elim (PV_Src_ResultControl.error_ne_ok _ _ h)
    | exact False.elim (PV_Src_ResultControl.same_residual_ne_ok _ _ h)
    | (pv_if h)
    | (have _test : Bool := value; cases value <;> simp only [Bool.false_eq_true,↓reduceIte] at h)
    | (have _test : core.ops.control_flow.ControlFlow _ _ := value; cases value <;> pv_head h)
'''
 s+=f'#print axioms {name}\n'
s+='end R1Z.PV_RunJoin_OuterConservation30\n';p=L/'PV_RunJoin_OuterConservation30.lean'
if '--check' in sys.argv:assert p.read_text()==s
else:p.write_text(s)
