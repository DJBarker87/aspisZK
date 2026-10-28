import PV_L2C_TraceRange
import PV_L2C_RecordRange
set_option autoImplicit false
noncomputable section
namespace PV_L2C_DirectCompilerRange
open Aeneas Aeneas.Std Result R1Z R0Z.WriterRefine
open PV_Src_NativeInput PV_Src_Forest_PrimitiveArguments
local instance : BuilderForestAdmissionPort.ExternalLinear := PV_RunJoin_ShippedExternal.E_shipped
local instance : BuilderForestAdmissionPort.Records := PV_RunJoin_UniversalRecords22.shipped
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

include K in
theorem records_public (i : Input)
    (success : run i = ok (.Ok i.compiled))
    (frontier : ∀ l : Fin 20, Canon8 i.snapshot.frontier.val[l.val]!)
    (ha : (forestPublic i.request).asset.val < 2147483647) :
    PV_L2C_TraceRange.PublicWords
      (wordPublic (PV_RunJoin_UniversalBuild22.records i).p) := by
  have hp := PV_RunJoin_UniversalRecords22.publicCorr (K:=K) i success
    frontier _ (PV_RunJoin_UniversalRecords22.newRecords i)
  refine ⟨ha,?_,?_⟩
  · intro n hn;exact hp.frontierCanon ⟨n,hn⟩
  · intro n hn;exact hp.emptyCanon ⟨n,hn⟩
#print axioms records_public

/- Exact raw returned compiler payload, not merely its field projection. -/
include K in
theorem source (i : Input)
    (success : run i = ok (.Ok i.compiled))
    (checked : PV_Src_RecordReference.Checked i)
    (frontier : ∀ l : Fin 20, Canon8 i.snapshot.frontier.val[l.val]!)
    (hf : PV_L2C_RecordRange.Fields i)
    (ha : (forestPublic i.request).asset.val < 2147483647) :
    (∀ c, c < 16 → (i.compiled.semantic_c1.c1.val[c]!).val.length = 1024) ∧
    ∀ c r, (PV_Src_Forest_Columns.read i.compiled.semantic_c1.c1 c r).val < 2147483647 := by
  let records := PV_RunJoin_UniversalBuild22.records i
  obtain ⟨banks,hbanks,hcached⟩ := PV_RunJoin_UniversalBuild22.returned_bank i success
  have hrun := PV_Src_ForestBanks.merged_run records banks hbanks
  obtain ⟨out,hout,hlength,hcells⟩ := PV_Src_ForestTrace.run_exact records.w records.p
  have same : out = banks.merged := Result.ok.inj (hout.symm.trans hrun)
  have hw := PV_L2C_RecordRange.records i checked hf
  have hp := records_public (K:=K) i success frontier ha
  rw [hcached,← same]
  refine ⟨hlength,?_⟩
  intro c r
  rw [hcells]
  exact PV_L2C_TraceRange.merged _ _ hw hp c r
#print axioms source
end PV_L2C_DirectCompilerRange
