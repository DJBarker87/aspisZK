from pathlib import Path
import sys
R=Path(__file__).resolve().parents[2];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
s='''import R1Z.PV_RunJoin_OuterChecked30
import R1Z.PV_RunJoin_CodecOuter30
import R1Z.PV_RunJoin_DecodedFrontier29
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CanonicalHonesty30
open Aeneas Aeneas.Std Result PV_RunJoin_Outer30 R0Z.WriterRefine
local instance : BuilderForestAdmissionPort.ExternalLinear := PV_RunJoin_ShippedExternal.E_shipped
local instance : BuilderForestAdmissionPort.Records := PV_RunJoin_UniversalRecords22.shipped
variable [LaneRoot]
'''
headers={}
for name,pt,wt,fn in [('transfer','PoolV1PrivateTransferPublicV1','PoolV1PairForestPrivateTransferWitnessV1','compile_pool_v1_pair_forest_private_transfer_merged_c1_v1'),('withdrawal','PoolV1WithdrawalPublicV1','PoolV1PairForestWithdrawalWitnessV1','compile_pool_v1_pair_forest_withdrawal_merged_c1_v1')]:
 header=f'''(bytes : Slice U8) (p : pool_v1.payment_relation.{pt})
    (w : pool_v1.pair_forest_trace.{wt})
    (context : pool_v1.payment_relation.PoolV1PaymentRelationContextV1)
    (snapshot : PV_RunJoin_CodecOuter30.Snapshot)
    (c : pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (h : PV_RunJoin_CodecOuter30.run bytes
      (pool_v1.pair_forest_trace.{fn} p w context) = ok (.Ok (snapshot,c)))'''
 headers[name]=header
 install=f'PV_RunJoin_OuterChecked30.{name}Input p w root (PV_RunJoin_CodecOuter30.snapshot snapshot) c'
 s+=f'''
theorem {name}_payload {header} :
    ∃ root, pool_v1.pair_forest_trace.lane_root w.input.pair = ok (.Ok root) ∧
      PV_Src_NativeInput.run ({install}) = ok (.Ok ({install}).compiled) ∧
      PV_Src_RecordReference.Checked ({install}) ∧
      ∀ l : Fin 20, Canon8 ({install}).snapshot.frontier.val[l.val]! := by
  obtain ⟨decoded,compiled⟩ := PV_RunJoin_CodecOuter30.returned bytes _ snapshot c h
  obtain ⟨root,hr,hn,hc⟩ := PV_RunJoin_OuterChecked30.{name} p w context _ c compiled
  refine ⟨root,hr,hn,hc,?_⟩
  intro l
  change Canon8 (PV_RunJoin_OuterABI30.snapshotToForest
    (PV_RunJoin_OuterABI30.snapshotFromForest
      (PV_RunJoin_DecodedArguments29.snapshot snapshot))).frontier.val[l.val]!
  rw [PV_RunJoin_OuterABI30.snapshot_roundtrip]
  exact PV_RunJoin_DecodedFrontier29.decoded_frontier bytes snapshot decoded l
#print axioms {name}_payload
'''
s+='''
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]
'''
for name,header in headers.items():
 install=f'PV_RunJoin_OuterChecked30.{name}Input p w root (PV_RunJoin_CodecOuter30.snapshot snapshot) c'
 s+=f'''
/-- All representation, cached-result and Checked obligations follow from the
canonical route. Semantic Admission remains explicit and is not inferred. -/
theorem {name}_honest_iff {header} :
    ∃ root, pool_v1.pair_forest_trace.lane_root w.input.pair = ok (.Ok root) ∧
      (PV_RunJoin_ConsumerBoundary25.HonestInput (K := K) ({install}) ↔
        PV_RunJoin_UniversalBuild22.Admission (K := K) ({install})) := by
  obtain ⟨root,hr,hn,hc,hf⟩ := {name}_payload bytes p w context snapshot c h
  refine ⟨root,hr,?_⟩
  exact ⟨fun hi => hi.1,fun ha => ⟨ha,hn,hc,hf⟩⟩
#print axioms {name}_honest_iff
'''
s+='end R1Z.PV_RunJoin_CanonicalHonesty30\n';p=L/'PV_RunJoin_CanonicalHonesty30.lean'
if '--check' in sys.argv:assert p.read_text()==s
else:p.write_text(s)
