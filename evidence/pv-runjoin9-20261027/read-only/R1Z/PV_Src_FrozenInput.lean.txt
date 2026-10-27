import R1Z.PV_Src_CanonicalSnapshot
import R1Z.PV_Src_CanonicalRoots
import R1Z.PV_Src_ExternalReference

/-! Canonical selected data with computed canonical snapshot and the explicit
P6-candidate frozen-root record dictionary. Compiled data remains data; source
execution success and relation/transport installation are not encoded here. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Src_FrozenInput
open Aeneas Aeneas.Std Result R0Z.WriterRefine R1J.SpendWitnessMap
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

structure Data where
  canonical : BuilderCanonical.Instance (K := K)
  index : U32
  indexBound : canonical.val.1.nextPairIndex < 2^64
  compiled : pair_forest_trace.PoolV1PairForestMergedC1CompilationV1
  laneAnchor : Array U32 8#usize
  pool : PV_Src_PublicRecords.Context
  domain : PV_Src_PublicRecords.Context
  destination : PV_Src_PublicRecords.Context

def encoded (i : Data (K := K)) : PV_Src_CheckedCanonical.Data (K := K) where
  canonical := i.canonical
  index := i.index
  snapshot := PV_Src_CanonicalSnapshot.native i.canonical.val.1 i.indexBound i.pool i.domain
  compiled := i.compiled
  laneAnchor := i.laneAnchor
  pool := i.pool
  domain := i.domain
  destination := i.destination

def input (i : Data (K := K)) : PV_Src_NativeInput.Input := PV_Src_CheckedCanonical.input (encoded i)

abbrev records : Records := PV_Src_RecordReference.withRoots PV_Src_CanonicalRoots.table
abbrev external : ExternalLinear := PV_Src_ExternalReference.dictionary

theorem checked (i : Data (K := K)) : PV_Src_RecordReference.Checked (input i) :=
  PV_Src_CheckedCanonical.checked (encoded i)

theorem frontier (i : Data (K := K)) (l : Fin 20) :
    Canon8 (input i).snapshot.frontier.val[l.val]! :=
  PV_Src_CanonicalSnapshot.frontier_canonical _ _ _ _ l

theorem words (i : Data (K := K)) (r : pair_forest_copy_builder.CopyRecords)
    (hr : @PV_Src_NativeInput.newRecords records (input i) = ok r) :
    WitnessOk (PV_Src_Forest_PrimitiveArguments.wordWitness r.w) :=
  PV_Src_RecordReference.words PV_Src_CanonicalRoots.table (input i) (checked i) r hr

#print axioms checked
#print axioms frontier
#print axioms words
end R1Z.PV_Src_FrozenInput
