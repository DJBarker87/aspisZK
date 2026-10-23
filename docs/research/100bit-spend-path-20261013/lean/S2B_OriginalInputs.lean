import S2B_FirstReturn

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.S2B_OriginalInputs
open AspisS2OwnedStage1 AspisS2OwnedStage1.SdkReference

/-- The range result of one indexed execution, on an original-byte frame.
The byte frame and actual range observation remain native obligations.
Original length gives both exact suffix width and full prefix/suffix split. -/
theorem proof_range {Execution : Type} (E : Execution)
    (read : Execution → alloc.vec.Vec U8) (selected : Execution → Slice U8)
    (original : alloc.vec.Vec U8) (frame : read E = original)
    (length : original.val.length = 58295)
    (range : alloc.vec.Vec.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      (read E) {start:=688#usize,«end»:=58295#usize} = ok (selected E)) :
    (selected E).val = (original.val.drop 688).take 57607 ∧
    (selected E).val.length = 57607 ∧
    original.val = original.val.take 688 ++ (selected E).val := by
  rw [frame] at range
  obtain ⟨suffix,hr,hs,hl⟩ := FrameOperationsTotal.compact_suffix_total original length
  have same := Result.ok.inj (range.symm.trans hr)
  rw [same]
  refine ⟨hs,hl,?_⟩
  have dropLength : (original.val.drop 688).length = 57607 := by
    rw [List.length_drop,length]
  have full : suffix.val = original.val.drop 688 := by
    rw [hs,←dropLength,List.take_length]
  rw [full]
  exact (List.take_append_drop 688 _).symm

/-- The two admitted instruction carriers determine the exact current-child
split argument. Runtime instruction admission is kept as the native frame. -/
theorem instruction_split {Execution : Type} (E : Execution)
    (data : Execution → alloc.vec.Vec U8) (ten : Bool)
    (frame : data E = ReadyCaller.instruction ten) :
    (data E).val = [3#u8,ReadyCaller.splitByte ten] ∧
    ((ten = true ∧ ReadyCaller.splitIndex ten = 10#usize) ∨
     (ten = false ∧ ReadyCaller.splitIndex ten = 11#usize)) := by
  constructor
  · rw [frame]; rfl
  · cases ten
    · exact Or.inr ⟨rfl,rfl⟩
    · exact Or.inl ⟨rfl,rfl⟩

#print axioms proof_range
#print axioms instruction_split
end AspisR1.S2B_OriginalInputs
