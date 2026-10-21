import R1Z.BuilderForestAdmissionPort
import R1Z.BuilderForestValidatorAcceptance
import R1Z.BuilderPartsComplete
import R1Z.BuilderDropStoreComposition

/-! Focused consequences of successful forest execution and a pointer-step
frame induction. Source-function identification and the relation from the
public entry points to RspendPlus are not hypotheses hidden by this module. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.BuilderForestAdmissionProgress
open Aeneas Aeneas.Std Result
open BuilderForestAdmissionPort BuilderRecordsFields
open BuilderForestAdmissionPort.pool_v1

/-- Successful helper execution supplies the actual record constructor and
the first selected-commitment comparison. No arbitrary record is chosen. -/
theorem compile_selected [ExternalLinear] [Records]
    (input : pair_forest_trace.PoolV1PairForestInputNoteWitnessV1)
    (out : U32) (recipient : Option payment_relation.PoolV1OutputNoteWitnessV1)
    (change : payment_relation.PoolV1OutputNoteWitnessV1)
    (publicInput : pair_forest_trace.ForestPublic)
    (anchor : Array aspis_core.field.M31 8#usize)
    (snapshot : pair_tree_profile.PoolV1PairLiveSnapshotV1)
    (compiled : pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (h : pair_forest_trace.compile_forest_from_copies input out recipient change
      publicInput anchor snapshot = ok (.Ok compiled)) :
    ∃ records selected leaf,
      pair_forest_copy_builder.CopyRecords.new input out recipient change snapshot
        publicInput.asset = ok records ∧
      pair_tree_profile.PoolV1PairLeafWitnessV1.selected_commitment
        input.pair.pair_leaf input.pair.selected_second = ok selected ∧
      pair_forest_copy_builder.CopyRecords.input_leaf records = ok leaf ∧
      core.cmp.impls.PartialEqShared.ne
        (R1Z.BuilderForestStdPort.Array.Insts.CoreCmpPartialEqArray
          8#usize aspis_core.field.M31.Insts.CoreCmpPartialEqM31)
        selected leaf = ok false := by
  unfold pair_forest_trace.compile_forest_from_copies at h
  obtain ⟨records, hr, h⟩ := bind_ok_inv h
  obtain ⟨selected, hs, h⟩ := bind_ok_inv h
  obtain ⟨leaf, hl, h⟩ := bind_ok_inv h
  obtain ⟨bad, hb, h⟩ := bind_ok_inv h
  cases bad with
  | false => exact ⟨records, selected, leaf, hr, hs, hl, hb⟩
  | true => simp at h

open BuilderDropObservation BuilderDropFields

/-- Pointer cursor model: the next aligned M31 word is four bytes later.
CONT11's solver receipt checks the actual std IterMut next-pointer and
remaining-length transition for every suffix of a 1024-word column. -/
def runPointer (store : Nat → Memory → Memory) : Nat → Nat → Memory → Memory
  | 0, _, memory => memory
  | n+1, base, memory => runPointer store n (base+4) (store base memory)

theorem pointer_frame (store : Nat → Memory → Memory)
    (contract : ∀ base, Frame (wordBytes base) (store base))
    (n base : Nat) : Frame (columnBytes base n) (runPointer store n base) := by
  induction n generalizing base with
  | zero => intro memory j _; rfl
  | succ n ih =>
    intro memory j hj
    have outside : ¬ (base ≤ j ∧ j < base+4*(n+1)) := by
      simpa only [column_bytes] using hj
    have head : j ∉ wordBytes base := by rw [word_bytes]; omega
    have tail : j ∉ columnBytes (base+4) n := by rw [column_bytes]; omega
    exact (ih (base+4) (store base memory) j tail).trans
      (contract base memory j head)

def runPointerFields (store : Nat → Memory → Memory) :
    List (Nat × Nat) → Memory → Memory
  | [], memory => memory
  | f::rest, memory =>
    runPointerFields store rest (runPointer store f.2 f.1 memory)

theorem pointer_fields_frame (store : Nat → Memory → Memory)
    (contract : ∀ base, Frame (wordBytes base) (store base))
    (fields : List (Nat × Nat)) :
    Frame (fieldsBytes fields) (runPointerFields store fields) := by
  induction fields with
  | nil => intro memory j _; rfl
  | cons f rest ih =>
    exact frame_compose (columnBytes f.1 f.2) (fieldsBytes rest)
      (runPointer store f.2 f.1) (runPointerFields store rest)
      (pointer_frame store contract f.2 f.1) ih

theorem pointer_fields_observation (store : Nat → Memory → Memory)
    (contract : ∀ base, Frame (wordBytes base) (store base))
    (fields : List (Nat × Nat)) (output : List Nat) (memory : Memory)
    (disjoint : ∀ j ∈ output, j ∉ fieldsBytes fields) :
    observe output (runPointerFields store fields memory) = observe output memory := by
  unfold observe
  apply List.map_congr_left
  intro j hj
  exact pointer_fields_frame store contract fields memory j (disjoint j hj)

#print axioms compile_selected
#print axioms pointer_frame
#print axioms pointer_fields_frame
#print axioms pointer_fields_observation
end R1Z.BuilderForestAdmissionProgress
