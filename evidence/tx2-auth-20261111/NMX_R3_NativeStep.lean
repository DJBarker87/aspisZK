import NMX_R3_NativeFrame
set_option autoImplicit false
namespace NMX_R3_NativeStep
open Aeneas Aeneas.Std Result NMX_R3_FrontierWords
local instance : Inhabited Row := ⟨Array.repeat 8#usize 0#u32⟩

/-- Source-iteration association at the actual child window. `selected` is the
universal-coordinate postcondition of NMX_assign; `frame` is NDB's iterator
write/frame postcondition. `empty` is obtained on the nonrejecting branch of
NMX_guard. These are segment outcomes, not extra row-input clauses. -/
theorem accepted (t : Slice U8) (next : U64) (before after : Frontier)
 (i : Usize) (row : Row) (tag : U64) (index : i.val < 20)
 (child : ∀ addr : Usize, addr.val=48+32*i.val → NCV_Reference.digest t addr=ok (.Ok row))
 (shift : next >>> i=ok tag)
 (empty : tag &&& 1#u64=0#u64 → row=NCV_ArrayFrame.coord NCV_Reference.EMPTY i.val)
 (selected : ∀ c, c < (8#usize).val →
  NCV_ArrayFrame.coord (NCV_ArrayFrame.coord after i.val) c = NCV_ArrayFrame.coord row c)
 (frame : ∀ j, j < (20#usize).val → j ≠ i.val → ∀ c, c < (8#usize).val →
  NCV_ArrayFrame.coord (NCV_ArrayFrame.coord after j) c =
  NCV_ArrayFrame.coord (NCV_ArrayFrame.coord before j) c) :
 ∃ successor : Usize, successor.val=i.val+1 ∧
 NCV_Reference.decode_frontier_loop.body t next before i = ok (.cont (after,successor)) := by
 have full := NMX_R3_NativeFrame.write_unique before after i row index selected frame
 obtain ⟨successor,advance,step⟩ := NMX_R3_PrimaryFrontierStep.step t next before i row tag
  index child shift empty
 exact ⟨successor,advance,by rw [full]; exact step⟩

/-- Digest error and vacant-node mismatch terminate at this same iteration,
for every arbitrary preceding frontier. Internal writes before rejection have
no returned state, allocation or event. -/
theorem rejected (t : Slice U8) (next : U64) (cap : t.val.length ≤ 768)
 (extent : 688 ≤ t.val.length) (bad : Nat) (bound : bad < 20)
 (rejected : ¬ At t next bad) (before : Frontier) (i : Usize) (same : i.val=bad) :
 NCV_Reference.decode_frontier_loop.body t next before i = ok (.done (.Err ())) :=
 NMX_R3_FrontierFailure.step t next cap extent bad bound rejected before i same
#print axioms accepted
#print axioms rejected
end NMX_R3_NativeStep
