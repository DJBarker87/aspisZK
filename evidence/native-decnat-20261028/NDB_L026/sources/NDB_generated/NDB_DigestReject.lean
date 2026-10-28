import NDB_RejectWitness
import NCV_ArrayFrame
set_option autoImplicit false
namespace NDB_DigestReject
open Aeneas Aeneas.Std Result

theorem step (b : Slice U8) (s i : Usize) (a : Array U32 8#usize) (word : U32)
    (cap : b.val.length ≤ 768) (fit : s.val+32 ≤ b.val.length) (index : i.val<8)
    (read : ∀ addr : Usize, addr.val=s.val+4*i.val → NCV_Reference.word32 b addr=ok word) :
    ∃ next : Usize, next.val=i.val+1 ∧ NCV_Reference.digest_loop.body b s a i=
      ok (if word.val<2147483647 then .cont (a.set i word,next)
          else .done (a,some (.Err ()))) := by
  have sm : (4#usize*i : Result Usize) ⦃ x=>x.val=4*i.val ⦄ := by
    apply UScalar.mul_spec <;> scalar_tac
  obtain ⟨offset,mul,offval⟩:=WP.spec_imp_exists sm
  have sa : (s+offset : Result Usize) ⦃ x=>x.val=s.val+offset.val ⦄ := by
    apply UScalar.add_spec <;> scalar_tac
  obtain ⟨addr,add,addrval⟩:=WP.spec_imp_exists sa
  have value:=read addr (by omega)
  obtain ⟨next,advance,nextval⟩:=NCV_Loop.advance i (by omega)
  obtain ⟨out,write,outval⟩:=WP.spec_imp_exists (Array.update_spec a i word (by scalar_tac))
  subst out
  refine ⟨next,nextval,?_⟩
  have lt : i<8#usize := by scalar_tac
  by_cases canonical : word.val<2147483647
  · have guard : ¬word>=2147483647#u32 := by scalar_tac
    simp only [NCV_Reference.digest_loop.body,lt,ite_true,mul,add,value,bind_tc_ok,
      guard,ite_false,write,advance,canonical]
  · have guard : word>=2147483647#u32 := by scalar_tac
    simp only [NCV_Reference.digest_loop.body,lt,ite_true,mul,add,value,bind_tc_ok,
      guard,canonical,ite_false]

theorem rejected (b : Slice U8) (s : Usize) (word : Nat → U32) (bad : Nat)
    (cap : b.val.length ≤ 768) (fit : s.val+32 ≤ b.val.length) (bound : bad<8)
    (read : ∀ i : Usize, i.val ≤ bad → ∀ addr : Usize,
      addr.val=s.val+4*i.val → NCV_Reference.word32 b addr=ok (word i.val))
    (canonical : ∀ j, j<bad → (word j).val<2147483647)
    (failure : ¬(word bad).val<2147483647) : NCV_Reference.digest b s=ok (.Err ()) := by
  have steps : ∀ a (i : Usize), i.val<bad → ∃ next : Usize, ∃ out : Array U32 8#usize,
      next.val=i.val+1 ∧ NCV_Reference.digest_loop.body b s a i=ok (.cont (out,next)) := by
    intro a i hi
    obtain ⟨next,nv,call⟩:=step b s i a (word i.val) cap fit (by omega) (read i (by omega))
    exact ⟨next,a.set i (word i.val),nv,by simpa only [canonical i.val hi,ite_true] using call⟩
  have reject : ∀ a (i : Usize), i.val=bad → ∃ out,
      NCV_Reference.digest_loop.body b s a i=ok (.done out) ∧ out.2=some (.Err ()) := by
    intro a i hi
    obtain ⟨next,nv,call⟩:=step b s i a (word i.val) cap fit (by omega) (read i (by omega))
    refine ⟨(a,some (.Err ())),?_,rfl⟩
    simpa only [hi,failure,ite_false] using call
  obtain ⟨out,call,post⟩:=NDB_RejectWitness.run
    (fun (a,i)=>NCV_Reference.digest_loop.body b s a i) bad
    (fun out=>out.2=some (.Err ())) steps reject (Array.repeat 8#usize 0#u32) 0#usize (by scalar_tac)
  have loopcall : NCV_Reference.digest_loop b s (Array.repeat 8#usize 0#u32) 0#usize=ok out := call
  unfold NCV_Reference.digest
  rw [loopcall]
  simp only [bind_tc_ok]
  rw [post]
#print axioms step
#print axioms rejected
end NDB_DigestReject
