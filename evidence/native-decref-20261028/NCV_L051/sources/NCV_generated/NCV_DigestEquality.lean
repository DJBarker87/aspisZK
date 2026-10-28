import NCV_ScanRun
import NCV_ArrayRead
import NCV_CastRef.Funs
set_option autoImplicit false
namespace NCV_DigestEquality
open Aeneas Aeneas.Std Result

theorem reflexive (a : Array U32 8#usize) : NCV_CastRef.eq_digest a a=ok true := by
  have steps : ∀ i : Usize, i.val<8 → ∃ next : Usize, next.val=i.val+1 ∧
      NCV_CastRef.eq_digest_loop.body a a i=ok (.cont next) := by
    intro i hi
    obtain ⟨next,advance,value⟩:=NCV_Loop.advance i (by omega)
    have lt : i<8#usize := by scalar_tac
    have read:=NCV_ArrayRead.read a i hi
    have no : (NCV_ArrayFrame.coord a i.val != NCV_ArrayFrame.coord a i.val)=false := by simp
    refine ⟨next,value,?_⟩
    simp only [NCV_CastRef.eq_digest_loop.body,lt,ite_true,read,bind_tc_ok,no,Bool.false_eq_true,ite_false,advance]
  have done : ∀ i : Usize, 8 ≤ i.val → NCV_CastRef.eq_digest_loop.body a a i=ok (.done none) := by
    intro i hi
    have no : ¬i<8#usize := by scalar_tac
    simp only [NCV_CastRef.eq_digest_loop.body,no,ite_false]
  have call : NCV_CastRef.eq_digest_loop a a 0#usize=ok none := by
    unfold NCV_CastRef.eq_digest_loop
    exact NCV_ScanRun.run_none _ 8 steps done _ (by scalar_tac)
  simp only [NCV_CastRef.eq_digest,call,bind_tc_ok]

theorem of_eq (a b : Array U32 8#usize) (same : a=b) : NCV_CastRef.eq_digest a b=ok true := by
  rw [same]
  exact reflexive b

#print axioms reflexive
#print axioms of_eq
end NCV_DigestEquality
