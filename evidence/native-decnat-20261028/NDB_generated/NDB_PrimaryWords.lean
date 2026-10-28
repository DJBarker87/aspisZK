import NCV_ArrayFrame
set_option autoImplicit false
namespace NDB_PrimaryWords
open Aeneas Aeneas.Std Result

def window (b : Slice U8) (s : Nat) (n : Usize) : Array U8 n :=
  ⟨List.ofFn (fun i : Fin n.val => NCV_ZeroStep.byte b (s+i.val)),by simp⟩

theorem add_read (b : Slice U8) (s k : Usize) (fit : s.val+k.val<b.val.length) :
    ∃ addr : Usize, s+k=ok addr ∧
      Slice.index_usize b addr=ok (NCV_ZeroStep.byte b (s.val+k.val)) := by
  have spec : (s+k : Result Usize) ⦃ x=>x.val=s.val+k.val ⦄ := by
    apply UScalar.add_spec <;> scalar_tac
  obtain ⟨addr,call,value⟩:=WP.spec_imp_exists spec
  refine ⟨addr,call,?_⟩
  simpa only [value] using NCV_ZeroStep.read b addr (by omega)

theorem word32 (b : Slice U8) (s : Usize) (fit : s.val+4 ≤ b.val.length) :
    NCV_Reference.word32 b s=ok (core.num.U32.from_le_bytes (window b s.val 4#usize)) := by
  have rd0:=NCV_ZeroStep.read b s (by omega)
  obtain ⟨addr1,add1,rd1⟩:=add_read b s 1#usize (by scalar_tac)
  obtain ⟨addr2,add2,rd2⟩:=add_read b s 2#usize (by scalar_tac)
  obtain ⟨addr3,add3,rd3⟩:=add_read b s 3#usize (by scalar_tac)
  simp only [NCV_Reference.word32,rd0,add1,rd1,add2,rd2,add3,rd3,bind_tc_ok]
  rfl

theorem word64 (b : Slice U8) (s : Usize) (fit : s.val+8 ≤ b.val.length) :
    NCV_Reference.word64 b s=ok (core.num.U64.from_le_bytes (window b s.val 8#usize)) := by
  have rd0:=NCV_ZeroStep.read b s (by omega)
  obtain ⟨addr1,add1,rd1⟩:=add_read b s 1#usize (by scalar_tac)
  obtain ⟨addr2,add2,rd2⟩:=add_read b s 2#usize (by scalar_tac)
  obtain ⟨addr3,add3,rd3⟩:=add_read b s 3#usize (by scalar_tac)
  obtain ⟨addr4,add4,rd4⟩:=add_read b s 4#usize (by scalar_tac)
  obtain ⟨addr5,add5,rd5⟩:=add_read b s 5#usize (by scalar_tac)
  obtain ⟨addr6,add6,rd6⟩:=add_read b s 6#usize (by scalar_tac)
  obtain ⟨addr7,add7,rd7⟩:=add_read b s 7#usize (by scalar_tac)
  simp only [NCV_Reference.word64,rd0,add1,rd1,add2,rd2,add3,rd3,add4,rd4,add5,rd5,add6,rd6,add7,rd7,bind_tc_ok]
  rfl

#print axioms add_read
#print axioms word32
#print axioms word64
end NDB_PrimaryWords
