import NCV_ArrayRun
import NCV_Reference.Funs
set_option autoImplicit false
namespace NDB_PrimarySequence
open Aeneas Aeneas.Std Result
/-- Primary E008 loop, with the word child observation quantified only over reached rows. -/
theorem step (b : Slice U8) (s i : Usize) (a : Array U64 8#usize)
    (row : U64) (cap : b.val.length ≤ 768) (fit : s.val+64 ≤ b.val.length)
    (index : i.val<8)
    (read : ∀ addr : Usize, addr.val=s.val+8*i.val → NCV_Reference.word64 b addr=ok row) :
    ∃ next : Usize, next.val=i.val+1 ∧
      NCV_Reference.sequences_loop.body b s a i=ok (.cont (a.set i row,next)) := by
  have sm : (8#usize*i : Result Usize) ⦃ x=>x.val=8*i.val ⦄ := by
    apply UScalar.mul_spec <;> scalar_tac
  obtain ⟨offset,mul,offval⟩:=WP.spec_imp_exists sm
  have sa : (s+offset : Result Usize) ⦃ x=>x.val=s.val+offset.val ⦄ := by
    apply UScalar.add_spec <;> scalar_tac
  obtain ⟨addr,add,addrval⟩:=WP.spec_imp_exists sa
  have word:=read addr (by omega)
  obtain ⟨next,advance,nextval⟩:=NCV_Loop.advance i (by omega)
  obtain ⟨out,write,outval⟩:=WP.spec_imp_exists
    (Array.update_spec a i row (by scalar_tac))
  subst out
  refine ⟨next,nextval,?_⟩
  have h : i<8#usize := by scalar_tac
  simp only [NCV_Reference.sequences_loop.body,h,ite_true,mul,add,word,write,advance,bind_tc_ok]

theorem terminal (b : Slice U8) (s i : Usize) (a : Array U64 8#usize)
    (index : 8 ≤ i.val) : NCV_Reference.sequences_loop.body b s a i=ok (.done a) := by
  have h : ¬i<8#usize := by scalar_tac
  simp only [NCV_Reference.sequences_loop.body,h,ite_false]

theorem value (b : Slice U8) (s : Usize) (target : Array U64 8#usize)
    (cap : b.val.length ≤ 768) (fit : s.val+64 ≤ b.val.length)
    (fields : ∀ i : Usize, i.val<8 → ∀ addr : Usize,
      addr.val=s.val+8*i.val → NCV_Reference.word64 b addr=ok (NCV_ArrayFrame.coord target i.val)) :
    NCV_Reference.sequences b s=ok target := by
  have steps : ∀ a i, i.val<(8#usize).val → ∃ next : Usize, next.val=i.val+1 ∧
      NCV_Reference.sequences_loop.body b s a i=
        ok (.cont (a.set i (NCV_ArrayFrame.coord target i.val),next)) := by
    intro a i hi
    exact step b s i a _ cap fit hi (fields i hi)
  unfold NCV_Reference.sequences NCV_Reference.sequences_loop
  exact NCV_ArrayRun.run (fun (a,i)=>NCV_Reference.sequences_loop.body b s a i)
    target id steps (fun a i h=>terminal b s i a h)
    _ 0#usize (by scalar_tac) (by intro j h; have hz : (0#usize).val=0 := rfl; rw [hz] at h; omega)
#print axioms step
#print axioms terminal
#print axioms value
end NDB_PrimarySequence
