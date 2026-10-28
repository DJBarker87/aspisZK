from pathlib import Path
import sys
R=Path(__file__).resolve().parents[2];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
s='''import R1Z.PV_RunJoin_OuterSnapshotBinding30
import R1Z.PV_RunJoin_OuterPrefix30
import R1Z.PV_RunJoin_OuterReturns30
import R1Z.PV_RunJoin_OuterConservation30
import R1Z.PV_RunJoin_OuterInnerPath30
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OuterReady30
open Aeneas Aeneas.Std Result PV_RunJoin_Outer30

theorem word_nonzero (n : U32) (h : 0<n.val) : n≠0#u32 := by
  intro he
  have hv := congrArg (fun x : U32 => x.val) he
  change n.val=0 at hv
  omega
#print axioms word_nonzero

theorem word_bound (n : U32) (h : n.val<2^30) : ¬ n≥1073741824#u32 := by
  have hh : ¬1073741824≤n.val := by omega
  simpa only [UScalar.le_equiv,UScalar.ofNatCore_val_eq] using hh
#print axioms word_bound

variable [LaneRoot] [BuilderForestAdmissionPort.ExternalLinear] [BuilderForestAdmissionPort.Records]
'''
for name,cap,p,w,f,val in [('transfer','Transfer','PoolV1PrivateTransferPublicV1','PoolV1PairForestPrivateTransferWitnessV1','compile_pool_v1_pair_forest_private_transfer_merged_c1_v1','validate_pool_v1_private_transfer_public_v1'),('withdrawal','Withdrawal','PoolV1WithdrawalPublicV1','PoolV1PairForestWithdrawalWitnessV1','compile_pool_v1_pair_forest_withdrawal_merged_c1_v1','validate_pool_v1_withdrawal_public_v1')]:
 out='w.recipient.value' if name=='transfer' else 'p.amount';rec='(some w.recipient)' if name=='transfer' else 'none';pc='some p.recipient_commitment' if name=='transfer' else 'none'
 pub=f'⟨p.anchor_root,p.nullifier,{pc},p.change_commitment,p.asset_id⟩'
 args=f'w.input {out} {rec} w.change ({pub}) root snapshot'
 cons=f'w.input.pair.value {out} w.change.value'
 params=f'''(p : pool_v1.payment_relation.{p})
    (w : pool_v1.pair_forest_trace.{w})
    (context : pool_v1.payment_relation.PoolV1PaymentRelationContextV1)
    (snapshot : pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1)'''
 s+=f'''
/-- Exact nonrecursive outer guards and the named inner path; no whole
wrapper call or semantic Admission premise is stored here. -/
structure {cap}Ready {params} (root : Array U32 8#usize) : Prop where
  lane : pool_v1.pair_forest_trace.lane_root w.input.pair = ok (.Ok root)
  statement : pool_v1.payment_relation.{val} {{p with anchor_root := root}} = ok (.Ok ())
  runtime : pool_v1.pair_trace.validate_common p.pool p.deployment_domain p.anchor_sequence
    root p.nullifier p.asset_id w.input.pair
    {{context with runtime_binding := {{context.runtime_binding with anchor_root := root}}}} = ok (.Ok ())
  pool_binding : snapshot.pool=p.pool
  domain_binding : snapshot.deployment_domain=p.deployment_domain
  conservation : PV_RunJoin_Conservation29.{name}Domain {cons}
  inner : PV_RunJoin_OuterInnerPath30.Path {args}

theorem {name}_iff {params} :
    (∃ c, pool_v1.pair_forest_trace.{f} p w context snapshot = ok (.Ok c)) ↔
      ∃ root, {cap}Ready p w context snapshot root := by
  constructor
  · rintro ⟨c,h⟩
    obtain ⟨root,hr,hc⟩ := PV_RunJoin_OuterReturns30.{name}_inner p w context snapshot c h
    obtain ⟨other,ho,hp,hv⟩ := PV_RunJoin_OuterPrefix30.{name} p w context snapshot c h
    have he : root=other := Aeneas.Std.core.result.Result.Ok.inj (Result.ok.inj (hr.symm.trans ho))
    subst other
    have hb := PV_RunJoin_OuterSnapshotBinding30.{name} p w context snapshot c h
    have balance := PV_RunJoin_OuterConservation30.{name} p w context snapshot c h
    refine ⟨root,⟨hr,hp,hv,hb.1,hb.2,balance,?_⟩⟩
    apply (PV_RunJoin_CompilerDomainProof28.success_iff _ _ _ _ _ _ _).mp
    exact ⟨_,hc⟩
  · rintro ⟨root,ready⟩
    obtain ⟨c,hc⟩ := (PV_RunJoin_OuterCall30.inner_success_iff {args}).mpr ready.inner
    refine ⟨c,?_⟩
    unfold pool_v1.pair_forest_trace.{f}
    rw [ready.lane]
    simp only [bind_tc_ok,Aeneas.Std.core.result.Result.Insts.CoreOpsTry.branch]
    rw [ready.statement]
    simp only [bind_tc_ok,PV_RunJoin_Outer30.core.result.Result.map_err,
      BuilderAdmissionStd.mapErr,Aeneas.Std.core.result.Result.Insts.CoreOpsTry.branch]
    simp only [pool_v1.pair_forest_trace.temporary_context,bind_tc_ok]
    rw [ready.runtime]
    simp only [bind_tc_ok,Aeneas.Std.core.result.Result.Insts.CoreOpsTry.branch]
    have bp : Aeneas.Std.core.array.equality.PartialEqArray.ne Aeneas.Std.core.cmp.PartialEqU8 snapshot.pool p.pool = ok false := by
      rw [PV_RunJoin_RuntimePrimitives30.bytes_ne,ready.pool_binding]
      simp
    rw [bp]
    simp only [bind_tc_ok,Bool.false_eq_true,↓reduceIte]
    have bd : Aeneas.Std.core.array.equality.PartialEqArray.ne Aeneas.Std.core.cmp.PartialEqU8 snapshot.deployment_domain p.deployment_domain = ok false := by
      rw [PV_RunJoin_RuntimePrimitives30.bytes_ne,ready.domain_binding]
      simp
    rw [bd]
    simp only [bind_tc_ok,Bool.false_eq_true,↓reduceIte]
'''
 if name=='transfer':
  s+='''    rw [if_neg (word_nonzero _ ready.conservation.1),if_neg (word_nonzero _ ready.conservation.2.1)]
    simp only [spend.VALUE_LIMIT,bind_tc_ok]
    rw [if_neg (word_bound _ ready.conservation.2.2.1),if_neg (word_bound _ ready.conservation.2.2.2.1)]
    have ha := (PV_RunJoin_CheckedAdd30.iff_value _ _ _).mpr ready.conservation.2.2.2.2
'''
 else:
  s+='''    rw [if_neg (word_nonzero _ ready.conservation.1)]
    simp only [spend.VALUE_LIMIT,bind_tc_ok]
    rw [if_neg (word_bound _ ready.conservation.2.1)]
    have ha := (PV_RunJoin_CheckedAdd30.iff_value _ _ _).mpr ready.conservation.2.2
'''
 s+='''    rw [ha]
    simp only [lift,bind_tc_ok]
    have ho := (PV_RunJoin_CheckedAdd30.option_ne_false (some w.input.pair.value) (some w.input.pair.value)).mpr rfl
    rw [ho]
    simp only [bind_tc_ok,Bool.false_eq_true,↓reduceIte]
    exact hc
'''
 s+=f'#print axioms {name}_iff\n'
s+='end R1Z.PV_RunJoin_OuterReady30\n';p=L/'PV_RunJoin_OuterReady30.lean'
if '--check' in sys.argv:assert p.read_text()==s
else:p.write_text(s)
