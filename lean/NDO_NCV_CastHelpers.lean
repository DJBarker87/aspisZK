import NCV_CastRef.Funs
import NCV_EqualValue
import NCV_ZeroRun
import NDO_JHg_ArrayRead
set_option autoImplicit false
namespace NCV_CastHelpers
open Aeneas Aeneas.Std Result AspisR1
attribute [local instance] Classical.propDecidable

theorem equal (b v : Slice U8) (cap : b.val.length ≤ 768) :
    NCV_CastRef.equal b v=ok (decide (b.val=v.val)) := by
  have same : NCV_CastRef.equal b v=NCV_Reference.equal b v := rfl
  rw [same,NCV_EqualValue.value b v cap]

theorem zero (b : Slice U8) (cap : b.val.length ≤ 768) :
    NCV_CastRef.zero b=ok (decide (NCV_ZeroRun.AllZero b 0)) := by
  have same : NCV_CastRef.zero b=NCV_Reference.zero b := rfl
  rw [same,NCV_ZeroRun.value b cap]

theorem range (b : Slice U8) (s : Usize) (n : Usize)
    (fit : s.val+n.val ≤ b.val.length) :
    ∃ stop : Usize, s+n=ok stop ∧ stop.val=s.val+n.val ∧
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        b {start:=s,«end»:=stop}=ok (JHg_FieldRead.segment b s.val n.val) := by
  have spec : (s+n : Result Usize) ⦃ x=>x.val=s.val+n.val ⦄ := by
    apply UScalar.add_spec <;> scalar_tac
  obtain ⟨stop,call,value⟩ := WP.spec_imp_exists spec
  refine ⟨stop,call,value,?_⟩
  have h:=JHg_FieldRead.read b s stop (by omega) (by omega)
  have sub : stop.val-s.val=n.val := by omega
  simpa only [sub] using h

theorem bytes32 (b : Slice U8) (s : Usize) (a : Array U8 32#usize)
    (fit : s.val+32 ≤ b.val.length) (field : (b.val.drop s.val).take 32=a.val) :
    NCV_CastRef.bytes32 b s=ok a := by
  obtain ⟨stop,call,value,read⟩:=range b s 32#usize fit
  simp only [show (32#usize).val=32 from rfl] at read
  have cast:=JHg_ArrayRead.cast b s.val 32 32#usize a field
  simp only [NCV_CastRef.bytes32,call,read,cast,bind_tc_ok]

theorem word64 (b : Slice U8) (s : Usize) (a : Array U8 8#usize)
    (fit : s.val+8 ≤ b.val.length) (field : (b.val.drop s.val).take 8=a.val) :
    NCV_CastRef.word64 b s=ok (core.num.U64.from_le_bytes a) := by
  obtain ⟨stop,call,value,read⟩:=range b s 8#usize fit
  simp only [show (8#usize).val=8 from rfl] at read
  have cast:=JHg_ArrayRead.cast b s.val 8 8#usize a field
  simp only [NCV_CastRef.word64,call,read,cast,bind_tc_ok]

theorem word32 (b : Slice U8) (s : Usize) (a : Array U8 4#usize)
    (fit : s.val+4 ≤ b.val.length) (field : (b.val.drop s.val).take 4=a.val) :
    NCV_CastRef.word32 b s=ok (core.num.U32.from_le_bytes a) := by
  obtain ⟨stop,call,value,read⟩:=range b s 4#usize fit
  simp only [show (4#usize).val=4 from rfl] at read
  have cast:=JHg_ArrayRead.cast b s.val 4 4#usize a field
  simp only [NCV_CastRef.word32,call,read,cast,bind_tc_ok]

#print axioms equal
#print axioms zero
#print axioms range
#print axioms bytes32
#print axioms word64
#print axioms word32
end NCV_CastHelpers
