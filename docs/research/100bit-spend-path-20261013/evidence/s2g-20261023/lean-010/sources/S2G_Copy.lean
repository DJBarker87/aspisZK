import S2SdkCopyLoopTotalV1

/-! Total existing owned copy, specialized to the admitted equal-length cut.
The native typed-region correspondence remains S2C's explicit obligation. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.S2G.Copy
open AspisS2OwnedStage1.SdkReference

def copy (sdk : OwnedSdk) (slot : Usize) (source : Slice U8) : Result OwnedSdk := do
  let (reply,after) ← CopyLoop.copy_in_place sdk slot source
  match reply with
  | .Ok () => ok after
  | .Err _ => fail .panic

/-- Direct implication of CopyLoop.copy_in_place_total; no bound on payload
width and no recursive evaluation of the 1768-byte copy is needed. -/
theorem contract (sdk : OwnedSdk) (slot : Usize) (source : Slice U8)
    (valid : slot.val < sdk.data_cells.val.length)
    (sameLength : (sdk.data_cells.val[slot.val]).bytes.val.length = source.val.length) :
    copy sdk slot source = ok (CopyLoop.replaceBytes sdk slot
      (sdk.data_cells.val[slot.val]) source) := by
  obtain ⟨cell,actual,run⟩ := CopyLoop.copy_in_place_total sdk slot source valid
  subst cell
  simp only [copy,run,if_pos sameLength,bind_tc_ok]
  rfl

/-- Full record preservation follows from the existing replacement definition;
this is a model frame, not a native heap/allocator frame. -/
theorem records_frame (sdk : OwnedSdk) (slot : Usize) (cell : OwnedDataCell)
    (source : Slice U8) :
    (CopyLoop.replaceBytes sdk slot cell source).accounts = sdk.accounts ∧
    (CopyLoop.replaceBytes sdk slot cell source).lamports_cells = sdk.lamports_cells := by
  exact ⟨rfl,rfl⟩

#print axioms contract
#print axioms records_frame
end AspisR1.S2G.Copy
