import NCX_Reference.Funs
import NHY_SliceRead
import NHY_ExactArray
set_option autoImplicit false
namespace NHY_FieldRead
open Aeneas Aeneas.Std Result WP
theorem range (b : Slice U8) (s : Usize) (n : Usize)
    (fit : s.val+n.val ≤ b.val.length) :
    ∃ stop : Usize, s+n=ok stop ∧ stop.val=s.val+n.val ∧
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        b {start:=s,«end»:=stop}=ok (NHY_SliceRead.segment b s.val n.val) := by
  have spec : (s+n : Result Usize) ⦃ x=>x.val=s.val+n.val ⦄ := by
    apply UScalar.add_spec <;> scalar_tac
  obtain ⟨stop,call,value⟩ := WP.spec_imp_exists spec
  refine ⟨stop,call,value,?_⟩
  have h:=NHY_SliceRead.read b s stop (by omega) (by omega)
  have sub : stop.val-s.val=n.val := by omega
  simpa only [sub] using h

theorem bytes32 (b : Slice U8) (s : Usize) (a : Array U8 32#usize)
    (fit : s.val+32 ≤ b.val.length) (field : (b.val.drop s.val).take 32=a.val) :
    NCX_Reference.read32 b s=ok a := by
  obtain ⟨stop,call,value,read⟩:=range b s 32#usize fit
  simp only [show (32#usize).val=32 from rfl] at read
  have cast:=NHY_ExactArray.cast 32#usize (NHY_SliceRead.segment b s.val 32) a field
  simp only [NCX_Reference.read32,call,read,cast,bind_tc_ok]

theorem word64 (b : Slice U8) (s : Usize) (a : Array U8 8#usize)
    (fit : s.val+8 ≤ b.val.length) (field : (b.val.drop s.val).take 8=a.val) :
    NCX_Reference.word b s=ok (core.num.U64.from_le_bytes a) := by
  obtain ⟨stop,call,value,read⟩:=range b s 8#usize fit
  simp only [show (8#usize).val=8 from rfl] at read
  have cast:=NHY_ExactArray.cast 8#usize (NHY_SliceRead.segment b s.val 8) a field
  simp only [NCX_Reference.word,call,read,cast,bind_tc_ok]


#print axioms range
#print axioms bytes32
#print axioms word64
end NHY_FieldRead
