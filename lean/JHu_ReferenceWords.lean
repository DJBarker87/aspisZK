import JHu_ReferenceBytes
import Mathlib.Tactic.IntervalCases
set_option autoImplicit false
namespace AspisR1.JHu_ReferenceWords
open Aeneas Aeneas.Std Result

theorem field_byte {n : Usize} (b : Slice U8) (s : Usize) (a : Array U8 n)
    (field : (b.val.drop s.val).take n.val=a.val) (j : Nat) (hj : j<n.val) :
    NCV_ZeroStep.byte b (s.val+j)=NCV_ArrayFrame.coord a j := by
  have h:=congrArg (fun xs : List U8 => xs[j]?.getD 0#u8) field
  have ha : j<a.val.length := by rw [a.property];exact hj
  simpa only [List.getElem?_eq_getElem ha,Option.getD_some,List.getElem?_take,
    if_pos hj,List.getElem?_drop,NCV_ZeroStep.byte,NCV_ArrayFrame.coord] using h
#print axioms field_byte

theorem offset {n : Usize} (b : Slice U8) (s k : Usize) (a : Array U8 n)
    (cap : b.val.length ≤ 768) (fit : s.val+n.val ≤ b.val.length)
    (field : (b.val.drop s.val).take n.val=a.val) (hk : k.val<n.val) :
    ∃ addr : Usize, s+k=ok addr ∧ Slice.index_usize b addr=ok (NCV_ArrayFrame.coord a k.val) := by
  have spec : (s+k : Result Usize) ⦃ x=>x.val=s.val+k.val ⦄ := by
    apply UScalar.add_spec <;> scalar_tac
  obtain ⟨addr,call,value⟩:=WP.spec_imp_exists spec
  refine ⟨addr,call,?_⟩
  rw [NCV_ZeroStep.read b addr (by omega),value,field_byte b s a field k.val hk]
#print axioms offset

theorem word32 (b : Slice U8) (s : Usize) (a : Array U8 4#usize)
    (cap : b.val.length ≤ 768) (fit : s.val+4 ≤ b.val.length)
    (field : (b.val.drop s.val).take 4=a.val) :
    NCV_Reference.word32 b s=ok (core.num.U32.from_le_bytes a) := by
  have first : Slice.index_usize b s=ok (NCV_ArrayFrame.coord a 0) := by
    rw [NCV_ZeroStep.read b s (by omega)]
    simpa only [Nat.add_zero] using congrArg ok (field_byte b s a field 0 (by scalar_tac))
  obtain ⟨p1,add1,read1⟩:=offset b s 1#usize a cap fit field (by scalar_tac)
  obtain ⟨p2,add2,read2⟩:=offset b s 2#usize a cap fit field (by scalar_tac)
  obtain ⟨p3,add3,read3⟩:=offset b s 3#usize a cap fit field (by scalar_tac)
  have assembled : Array.make 4#usize [NCV_ArrayFrame.coord a 0, NCV_ArrayFrame.coord a 1, NCV_ArrayFrame.coord a 2, NCV_ArrayFrame.coord a 3]=a := by
    apply Subtype.ext
    apply List.ext_getElem
    · exact a.property.symm
    · intro j hj ha
      have bound : j<4 := by simpa using hj
      interval_cases j <;> simp only [NCV_ArrayFrame.coord,List.getElem?_eq_getElem (by omega : _ < a.val.length),Option.getD_some] <;> rfl
  simp only [NCV_Reference.word32,first,add1,read1,add2,read2,add3,read3,bind_tc_ok,show (1#usize).val=1 from rfl,show (2#usize).val=2 from rfl,show (3#usize).val=3 from rfl,show (4#usize).val=4 from rfl,show (5#usize).val=5 from rfl,show (6#usize).val=6 from rfl,show (7#usize).val=7 from rfl,assembled]
#print axioms word32

theorem word64 (b : Slice U8) (s : Usize) (a : Array U8 8#usize)
    (cap : b.val.length ≤ 768) (fit : s.val+8 ≤ b.val.length)
    (field : (b.val.drop s.val).take 8=a.val) :
    NCV_Reference.word64 b s=ok (core.num.U64.from_le_bytes a) := by
  have first : Slice.index_usize b s=ok (NCV_ArrayFrame.coord a 0) := by
    rw [NCV_ZeroStep.read b s (by omega)]
    simpa only [Nat.add_zero] using congrArg ok (field_byte b s a field 0 (by scalar_tac))
  obtain ⟨p1,add1,read1⟩:=offset b s 1#usize a cap fit field (by scalar_tac)
  obtain ⟨p2,add2,read2⟩:=offset b s 2#usize a cap fit field (by scalar_tac)
  obtain ⟨p3,add3,read3⟩:=offset b s 3#usize a cap fit field (by scalar_tac)
  obtain ⟨p4,add4,read4⟩:=offset b s 4#usize a cap fit field (by scalar_tac)
  obtain ⟨p5,add5,read5⟩:=offset b s 5#usize a cap fit field (by scalar_tac)
  obtain ⟨p6,add6,read6⟩:=offset b s 6#usize a cap fit field (by scalar_tac)
  obtain ⟨p7,add7,read7⟩:=offset b s 7#usize a cap fit field (by scalar_tac)
  have assembled : Array.make 8#usize [NCV_ArrayFrame.coord a 0, NCV_ArrayFrame.coord a 1, NCV_ArrayFrame.coord a 2, NCV_ArrayFrame.coord a 3, NCV_ArrayFrame.coord a 4, NCV_ArrayFrame.coord a 5, NCV_ArrayFrame.coord a 6, NCV_ArrayFrame.coord a 7]=a := by
    apply Subtype.ext
    apply List.ext_getElem
    · exact a.property.symm
    · intro j hj ha
      have bound : j<8 := by simpa using hj
      interval_cases j <;> simp only [NCV_ArrayFrame.coord,List.getElem?_eq_getElem (by omega : _ < a.val.length),Option.getD_some] <;> rfl
  simp only [NCV_Reference.word64,first,add1,read1,add2,read2,add3,read3,add4,read4,add5,read5,add6,read6,add7,read7,bind_tc_ok,show (1#usize).val=1 from rfl,show (2#usize).val=2 from rfl,show (3#usize).val=3 from rfl,show (4#usize).val=4 from rfl,show (5#usize).val=5 from rfl,show (6#usize).val=6 from rfl,show (7#usize).val=7 from rfl,assembled]
#print axioms word64
end AspisR1.JHu_ReferenceWords
