import R1Z.PV_Src_CanonicalNormalize
import R1Z.PV_Src_CheckedCanonical
import R1Z.PV_Src_PathBits

/-! A canonical selected carrier with path-consistent membership index. This
supplies representation data, not equality to the installed native caller.
The carrier allows arbitrary supplied snapshots; fixed-root bank stages remain
in FrozenStages and are not inferred here. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Src_PackedSelection
open Aeneas Aeneas.Std Result R1J.SpendWitnessMap
open BuilderForestAdmissionPort.pool_v1
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

def select (i : PV_Src_CheckedCanonical.Data (K := K)) : PV_Src_CheckedCanonical.Data (K := K) where
  canonical := PV_Src_CanonicalNormalize.normalize i.canonical
  index := PV_Src_PathIndex.index (PV_Src_CanonicalNormalize.normalize i.canonical).val.2
  snapshot := i.snapshot
  compiled := i.compiled
  laneAnchor := i.laneAnchor
  pool := i.pool
  domain := i.domain
  destination := i.destination

theorem public_preserved (i : PV_Src_CheckedCanonical.Data (K := K)) :
    (select i).canonical.val.1 = i.canonical.val.1 :=
  PV_Src_CanonicalNormalize.public_eq i.canonical

theorem index_bound (i : PV_Src_CheckedCanonical.Data (K := K)) : (select i).index.val < 2^20 :=
  PV_Src_PathIndex.bound _

theorem checked (i : PV_Src_CheckedCanonical.Data (K := K)) :
    PV_Src_RecordReference.Checked (PV_Src_CheckedCanonical.input (select i)) :=
  PV_Src_CheckedCanonical.checked _

theorem bits (i : PV_Src_CheckedCanonical.Data (K := K)) :
    BuilderRecordsPath.bits (PV_Src_NativeDirections.reference
      (PV_Src_CheckedCanonical.input (select i)).witness) =
      (BuilderCanonical.rustWitness (select i).canonical.val.2).bits :=
  PV_Src_PathBits.bits _

theorem primitive (roots : BuilderRecordsReference.Roots)
    (i : PV_Src_CheckedCanonical.Data (K := K)) :
    ∃ records,
      @PV_Src_NativeInput.newRecords (PV_Src_RecordReference.withRoots roots)
        (PV_Src_CheckedCanonical.input (select i)) = ok records ∧
      R0Z.WriterRefine.WitnessOk (PV_Src_Forest_PrimitiveArguments.wordWitness records.w) := by
  let input := PV_Src_CheckedCanonical.input (select i)
  refine ⟨PV_Src_RecordReference.returned roots input,
    PV_Src_RecordReference.newRecords_eq roots input,?_⟩
  exact PV_Src_RecordReference.words roots input (checked i) _
    (PV_Src_RecordReference.newRecords_eq roots input)

#print axioms public_preserved
#print axioms index_bound
#print axioms checked
#print axioms bits
#print axioms primitive
end R1Z.PV_Src_PackedSelection
