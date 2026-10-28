import R1Z.PV_RunJoin_RecordAppendLift31
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_RecordOutputLift31
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.BuilderModel
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
open PV_Src_Forest_PrimitiveArguments
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

theorem output (r : CopyRecords) (pub : R0P.Public K)
    (hw : WitnessOk (wordWitness r.w)) (hp : PubCorr (wordPublic r.p) pub)
    (d : Array U32 8#usize) (hd : CopyRecords.output_pair r = ok d) :
    Canon8 d ∧ digK d = outPair pub (toModel (wordWitness r.w)) := by
  unfold CopyRecords.output_pair at hd
  pv_peel hd with raw hr
  rw [PV_RunJoin_DigestIdentity30.digest] at hd
  cases Result.ok.inj hd
  rw [PV_Src_Forest_AppendArguments.output_pair] at hr
  obtain ⟨out,ho,hm,hc⟩ := outPair_lift (wordWitness r.w) (wordPublic r.p) pub hp hw
  rw [hr] at ho
  cases Result.ok.inj ho
  exact ⟨hc,funext hm⟩
#print axioms output
end R1Z.PV_RunJoin_RecordOutputLift31
