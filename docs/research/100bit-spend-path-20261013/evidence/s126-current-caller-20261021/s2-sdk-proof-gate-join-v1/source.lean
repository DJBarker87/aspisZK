import S2SdkProofGateTotalV1
import S2SdkProofPrefixParentV1
import S2FrameOperationsTotalV1
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisS2OwnedStage1.SdkReference.ProofGate

def takePrefix (bytes candidate : Slice U8) : Slice U8 :=
  ⟨bytes.val.take candidate.val.length,by
    have bound := bytes.property
    simp only [List.length_take]
    omega⟩

/-- The extracted full-buffer loop and the loop on its exact prefix consume
the same cells. Covers short inputs too; neither traversal success is assumed. -/
theorem prefix_take_eq (bytes candidate : Slice U8) :
    prefix_different bytes candidate=prefix_different (takePrefix bytes candidate) candidate := by
  obtain ⟨first,runFirst,semFirst⟩ := prefix_total bytes candidate
  obtain ⟨second,runSecond,semSecond⟩ := prefix_total (takePrefix bytes candidate) candidate
  have size : (takePrefix bytes candidate).val.length=
      min candidate.val.length bytes.val.length := by simp [takePrefix]
  have cells (j : Nat) (valid : j<candidate.val.length) :
      CellEq bytes candidate j ↔ CellEq (takePrefix bytes candidate) candidate j := by
    unfold CellEq takePrefix
    rw [List.getElem?_take_of_lt valid]
  have matching : first=false ↔ second=false := by
    rw [semFirst,semSecond]
    constructor
    · rintro ⟨long,all⟩
      refine ⟨by omega,?_⟩
      intro j valid
      exact (cells j valid).mp (all j valid)
    · rintro ⟨long,all⟩
      refine ⟨by omega,?_⟩
      intro j valid
      exact (cells j valid).mpr (all j valid)
  have equal : first=second := by cases first <;> cases second <;> simp_all
  rw [runFirst,runSecond,equal]

/-- Exact bridge to the prefix range operation actually present at both
complete owned caller sites. The reached proof length supplies the range bound. -/
theorem caller_prefix_eq (bytes : alloc.vec.Vec U8) (candidate : Array U8 688#usize)
    (length : bytes.val.length=58295) :
    ∃ selected,
      alloc.vec.Vec.index (core.slice.index.SliceIndexRangeToUsizeSlice U8)
        bytes {«end»:=688#usize}=ok selected ∧
      prefix_different (alloc.vec.Vec.deref bytes) (Array.to_slice candidate)=
        ProofPrefixParent.loopCmp selected candidate := by
  have candidateLength : (Array.to_slice candidate).val.length=688 := by
    simpa [Array.to_slice] using candidate.property
  have prefixVal : (takePrefix (alloc.vec.Vec.deref bytes) (Array.to_slice candidate)).val=
      bytes.val.take 688 := by
    simp only [takePrefix,candidateLength,FrameOperationsTotal.deref_val]
  have selected : FrameOperationsTotal.segment (alloc.vec.Vec.deref bytes) 0#usize 688#usize=
      takePrefix (alloc.vec.Vec.deref bytes) (Array.to_slice candidate) := by
    apply Subtype.ext
    simp [FrameOperationsTotal.segment,FrameOperationsTotal.deref_val,prefixVal]
  refine ⟨takePrefix (alloc.vec.Vec.deref bytes) (Array.to_slice candidate),?_,?_⟩
  · rw [←selected]
    exact FrameOperationsTotal.prefix_range_total bytes 688#usize (by scalar_tac)
  · rw [prefix_take_eq]
    unfold ProofPrefixParent.loopCmp scalarNe
    have exactLength : (takePrefix (alloc.vec.Vec.deref bytes) (Array.to_slice candidate)).val.length=
        (Array.to_slice candidate).val.length := by
      rw [prefixVal,candidateLength,List.length_take,length]
      decide
    rw [if_pos exactLength]

#print axioms prefix_take_eq
#print axioms caller_prefix_eq
end AspisS2OwnedStage1.SdkReference.ProofGate
