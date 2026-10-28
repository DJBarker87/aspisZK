import R1Z.PV_RunJoin_AppendDeterminism32
import R1Z.PV_RunJoin_RecordOutputLift31
import R1Z.PV_RunJoin_SemanticChange30
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OutputAgreement32
open Aeneas Aeneas.Std Result R0Z.WriterRefine R1J.SpendWitnessMap PV_Src_NativeInput
open PV_RunJoin_HonestIdentification26 PV_RunJoin_SemanticChange30
local instance : BuilderForestAdmissionPort.ExternalLinear := PV_RunJoin_ShippedExternal.E_shipped
local instance : BuilderForestAdmissionPort.Records := PV_RunJoin_UniversalRecords22.shipped
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

theorem output (i : Honest (K := K))
    (r : BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder.CopyRecords)
    (hr : newRecords i.val = ok r) (leaf : Array U32 8#usize)
    (hl : BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder.CopyRecords.output_pair r = ok leaf) :
    Canon8 leaf ∧ AspisR1.SpendRelation.outputPair (statement (K := K) i.val) = some (digK leaf) := by
  have hw := PV_RunJoin_UniversalRecords22.words i.val i.property.2.2.1 r hr
  have hp := PV_RunJoin_UniversalRecords22.publicCorr (K := K) i.val (success i) i.property.2.2.2 r hr
  obtain ⟨hc,hm⟩ := PV_RunJoin_RecordOutputLift31.output r (statement (K := K) i.val) hw hp leaf hl
  have he := BuilderSpendRelation.outputPair_eq (statement (K := K) i.val) (witness (K := K) i.val) (admitted i).1
  rw [PV_RunJoin_UniversalRecords22.returned i.val r hr] at hm
  unfold witness at he
  rw [BuilderFieldNormalization.decoded_witness] at he
  exact ⟨hc,he.trans (congrArg some hm.symm)⟩
#print axioms output

theorem unique (a b : Honest (K := K))
    (same : source_honest.public a=source_honest.public b)
    (ra rb : BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder.CopyRecords)
    (ha : newRecords a.val=ok ra) (hb : newRecords b.val=ok rb)
    (la lb : Array U32 8#usize)
    (hla : BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder.CopyRecords.output_pair ra=ok la)
    (hlb : BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder.CopyRecords.output_pair rb=ok lb) : la=lb := by
  obtain ⟨hca,hpa⟩ := output a ra ha la hla
  obtain ⟨hcb,hpb⟩ := output b rb hb lb hlb
  have pa := PV_RunJoin_UniversalPublic22.projection (K := K) (inputs (K := K)) PV_Src_Transport.transport a
  have pb := PV_RunJoin_UniversalPublic22.projection (K := K) (inputs (K := K)) PV_Src_Transport.transport b
  have hp : statement (K := K) a.val=statement b.val := pa.symm.trans (same.trans pb)
  rw [hp] at hpa
  exact PV_RunJoin_CanonicalWordEq31.digest (K := K) la lb hca hcb (Option.some.inj (hpa.symm.trans hpb))
#print axioms unique
end R1Z.PV_RunJoin_OutputAgreement32
