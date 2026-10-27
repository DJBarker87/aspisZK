import R1Z.PV_Src_CanonicalRequest
import R1Z.PV_Src_RecordDynamic

/-! Exact selected-input words condition for every canonical admitted witness.
Compilation, snapshot association, and installed transport remain separate.
This does not identify arbitrary native input data with a canonical witness. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Src_CheckedCanonical
open Aeneas Aeneas.Std Result R1J.SpendWitnessMap
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

structure Data where
  canonical : BuilderCanonical.Instance (K := K)
  index : U32
  snapshot : pair_tree_profile.PoolV1PairLiveSnapshotV1
  compiled : pair_forest_trace.PoolV1PairForestMergedC1CompilationV1
  laneAnchor : Array U32 8#usize
  pool : PV_Src_PublicRecords.Context
  domain : PV_Src_PublicRecords.Context
  destination : PV_Src_PublicRecords.Context

def input (i : Data (K := K)) : PV_Src_NativeInput.Input :=
  PV_Src_CheckedEncoding.input i.canonical.val.2
    (PV_Src_CanonicalRequest.request i.canonical i.pool i.domain i.destination)
    i.index i.snapshot i.compiled i.laneAnchor

theorem checked (i : Data (K := K)) : PV_Src_RecordReference.Checked (input i) :=
  PV_Src_CheckedEncoding.checked _ _ _ _ _ _
    (PV_Src_CanonicalRequest.output_value i.canonical i.pool i.domain i.destination)

theorem words [ExternalLinear] (i : Data (K := K))
    (r : pair_forest_copy_builder.CopyRecords)
    (h : @PV_Src_NativeInput.newRecords PV_Src_RecordDynamic.dictionary (input i) = ok r) :
    R0Z.WriterRefine.WitnessOk (PV_Src_Forest_PrimitiveArguments.wordWitness r.w) :=
  PV_Src_RecordDynamic.words (input i) (checked i) r h

#print axioms checked
#print axioms words
end R1Z.PV_Src_CheckedCanonical
