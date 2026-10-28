import NCX_Reference.Funs
import NCV_CastHelpers
set_option autoImplicit false
namespace NCX_FieldLaws
open Aeneas Aeneas.Std Result AspisR1
attribute [local instance] Classical.propDecidable

theorem equal (b v : Slice U8) (cap : b.val.length ≤ 768) :
    NCX_Reference.equal b v=ok (decide (b.val=v.val)) := by
  have same : NCX_Reference.equal b v=NCV_CastRef.equal b v := rfl
  rw [same,NCV_CastHelpers.equal b v cap]
theorem zero (b : Slice U8) (cap : b.val.length ≤ 768) :
    NCX_Reference.zero b=ok (decide (NCV_ZeroRun.AllZero b 0)) := by
  have same : NCX_Reference.zero b=NCV_CastRef.zero b := rfl
  rw [same,NCV_CastHelpers.zero b cap]
theorem read32 (b : Slice U8) (s : Usize) (a : Array U8 32#usize)
    (fit : s.val+32 ≤ b.val.length) (field : (b.val.drop s.val).take 32=a.val) :
    NCX_Reference.read32 b s=ok a := by
  have same : NCX_Reference.read32 b s=NCV_CastRef.bytes32 b s := rfl
  rw [same,NCV_CastHelpers.bytes32 b s a fit field]
theorem word (b : Slice U8) (s : Usize) (a : Array U8 8#usize)
    (fit : s.val+8 ≤ b.val.length) (field : (b.val.drop s.val).take 8=a.val) :
    NCX_Reference.word b s=ok (core.num.U64.from_le_bytes a) := by
  have same : NCX_Reference.word b s=NCV_CastRef.word64 b s := rfl
  rw [same,NCV_CastHelpers.word64 b s a fit field]

#print axioms equal
#print axioms zero
#print axioms read32
#print axioms word
end NCX_FieldLaws
