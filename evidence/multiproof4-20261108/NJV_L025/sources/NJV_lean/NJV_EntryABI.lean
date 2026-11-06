import NJV_AdoptedObservation

set_option autoImplicit false
noncomputable section
namespace NJV_EntryABI
open Aeneas Aeneas.Std Result NJP_DigestCarrier NJP_ScratchCarrier
open MultiproofConeRef

/-- Exact Rust entry arguments. Cursor is local, not an input selected by a
caller; native verify_in_place creates it as zero after the initial checks. -/
def initial (idx : Array U32 16#usize) (val : Array RefDigest 16#usize) (n : Usize) : reference.Scratch :=
 ⟨idx,val,n,0#usize⟩

theorem zero (idx : Array U32 16#usize) (val : Array RefDigest 16#usize) (n : Usize) :
 (initial idx val n).«at»=0#usize := rfl

/-- Rejected entry preserves every original input cell, independent of n. -/
theorem rejection (H : Slice (Slice U8) → RefDigest) (root : RefDigest) (physical : Slice U8)
    (idx : Array U32 16#usize) (val : Array RefDigest 16#usize) (n : Usize)
    (guard : ¬NJV_Entry.Guard physical (initial idx val n)) :
 AspisV8R19.MemoizedProgramLaw.eval H (NJV_Entry.program root physical (initial idx val n))=
 ([],ok (false,initial idx val n)) := by
 simp only [NJV_Entry.program,if_neg guard,AspisV8R19.MemoizedProgramLaw.eval]

#print zero
#print axioms zero
#print rejection
#print axioms rejection
end NJV_EntryABI
end
