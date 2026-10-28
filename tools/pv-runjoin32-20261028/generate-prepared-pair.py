from pathlib import Path
import sys
R=Path(__file__).resolve().parents[2];p=R/'docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RunJoin_PreparedPair32.lean'
s='''import R1Z.PV_RunJoin_CanonicalBinding32
import R1Z.PV_RunJoin_PreparedPublicAgreement32
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PreparedPair32
open Aeneas Aeneas.Std Result PV_RunJoin_Outer30 PV_RunJoin_HonestIdentification26
local instance : BuilderForestAdmissionPort.ExternalLinear := PV_RunJoin_ShippedExternal.E_shipped
local instance : BuilderForestAdmissionPort.Records := PV_RunJoin_UniversalRecords22.shipped
local instance : LaneRoot := PV_RunJoin_LaneABI31.native
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]
'''
for kind,title,fn in [('transfer','PrivateTransfer','private_transfer'),('withdrawal','Withdrawal','withdrawal')]:
 ia=f'PV_RunJoin_OuterChecked30.{kind}Input p wa rootA (PV_RunJoin_CodecOuter30.snapshot sa) ca'
 ib=f'PV_RunJoin_OuterChecked30.{kind}Input p wb rootB (PV_RunJoin_CodecOuter30.snapshot sb) cb'
 s+=f'''
/-- Two actual successful canonical preparations at the same raw public header:
complete native public agreement follows from common semantic statement.
No snapshot pool/domain agreement is left as a premise. The original returned
payloads remain distinct; their private traces are not asserted equal. -/
theorem {kind} (base : ProverRwFull.ExternalTypes) (ba bb : Slice U8)
    (p : pool_v1.payment_relation.PoolV1{title}PublicV1)
    (wa wb : pool_v1.pair_forest_trace.PoolV1PairForest{title}WitnessV1)
    (xa xb : pool_v1.payment_relation.PoolV1PaymentRelationContextV1)
    (sa sb : PV_RunJoin_CodecOuter30.Snapshot)
    (ca cb : pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (ha : PV_RunJoin_CodecOuter30.run ba
      (pool_v1.pair_forest_trace.compile_pool_v1_pair_forest_{fn}_merged_c1_v1 p wa xa) = ok (.Ok (sa,ca)))
    (hb : PV_RunJoin_CodecOuter30.run bb
      (pool_v1.pair_forest_trace.compile_pool_v1_pair_forest_{fn}_merged_c1_v1 p wb xb) = ok (.Ok (sb,cb)))
    : ∃ (rootA rootB : Array U32 8#usize)
      (hia : PV_RunJoin_ConsumerBoundary25.HonestInput (K := K) ({ia}))
      (hib : PV_RunJoin_ConsumerBoundary25.HonestInput (K := K) ({ib})),
      pool_v1.pair_forest_trace.lane_root wa.input.pair = ok (.Ok rootA) ∧
      pool_v1.pair_forest_trace.lane_root wb.input.pair = ok (.Ok rootB) ∧
      (source_honest.public (⟨{ia},hia⟩ : Honest (K := K)) =
       source_honest.public (⟨{ib},hib⟩ : Honest (K := K)) →
       PV_RunJoin_NominalPublicData.fromInput base ({ia}) =
       PV_RunJoin_NominalPublicData.fromInput base ({ib})) := by
  obtain ⟨rootA,hra,hia⟩ := PV_RunJoin_CanonicalHonest31.{kind} (K := K) ba p wa xa sa ca ha
  obtain ⟨rootB,hrb,hib⟩ := PV_RunJoin_CanonicalHonest31.{kind} (K := K) bb p wb xb sb cb hb
  refine ⟨rootA,rootB,hia,hib,hra,hrb,?_⟩
  intro same
  exact PV_RunJoin_PreparedPublicAgreement32.{kind} base ba bb p wa wb xa xb sa sb ca cb ha hb rootA rootB hia hib same
#print axioms {kind}
'''
s+='end R1Z.PV_RunJoin_PreparedPair32\n'
if '--check' in sys.argv:assert p.read_text()==s
else:p.write_text(s)
print('prepared pair generator verified' if '--check' in sys.argv else 'wrote prepared pair')
