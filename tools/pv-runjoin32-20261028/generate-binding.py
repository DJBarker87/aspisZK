from pathlib import Path
import sys
R=Path(__file__).resolve().parents[2];p=R/'docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RunJoin_CanonicalBinding32.lean'
s='''import R1Z.PV_RunJoin_CanonicalCoverage31
import R1Z.PV_RunJoin_OuterSnapshotBinding30
import R1Z.PV_RunJoin_PreparationContext32
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CanonicalBinding32
open Aeneas Aeneas.Std Result PV_RunJoin_Outer30
local instance : BuilderForestAdmissionPort.ExternalLinear := PV_RunJoin_ShippedExternal.E_shipped
local instance : BuilderForestAdmissionPort.Records := PV_RunJoin_UniversalRecords22.shipped
local instance : LaneRoot := PV_RunJoin_LaneABI31.native
'''
for kind,title,fn in [('transfer','PrivateTransfer','private_transfer'),('withdrawal','Withdrawal','withdrawal')]:
 s+=f'''
/-- Binding facts for the original successful canonical preparation, without
 assuming equality of its omitted context bytes. -/
theorem {kind} (bytes : Slice U8)
    (p : pool_v1.payment_relation.PoolV1{title}PublicV1)
    (w : pool_v1.pair_forest_trace.PoolV1PairForest{title}WitnessV1)
    (context : pool_v1.payment_relation.PoolV1PaymentRelationContextV1)
    (snapshot : PV_RunJoin_CodecOuter30.Snapshot)
    (c : pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (h : PV_RunJoin_CodecOuter30.run bytes
      (pool_v1.pair_forest_trace.compile_pool_v1_pair_forest_{fn}_merged_c1_v1 p w context) = ok (.Ok (snapshot,c))) :
    (PV_RunJoin_CodecOuter30.snapshot snapshot).pool=p.pool ∧
    (PV_RunJoin_CodecOuter30.snapshot snapshot).deployment_domain=p.deployment_domain ∧
    context.runtime_binding.pool=p.pool ∧
    context.runtime_binding.deployment_domain=p.deployment_domain ∧
    context.runtime_binding.anchor_sequence=p.anchor_sequence ∧
    context.runtime_binding.asset_id=p.asset_id := by
  have ho := (PV_RunJoin_CodecOuter30.returned bytes _ snapshot c h).2
  have hs := PV_RunJoin_OuterSnapshotBinding30.{kind} p w context _ c ho
  exact ⟨hs.1,hs.2,PV_RunJoin_PreparationContext32.{kind}_binding p w context _ c ho⟩
#print axioms {kind}
'''
s+='end R1Z.PV_RunJoin_CanonicalBinding32\n'
if '--check' in sys.argv:assert p.read_text()==s
else:p.write_text(s)
print('canonical binding generator verified' if '--check' in sys.argv else 'wrote canonical binding')
