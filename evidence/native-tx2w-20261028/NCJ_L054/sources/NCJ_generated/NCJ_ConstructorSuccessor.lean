import NCJ_ConstructorSuccessorCell
set_option autoImplicit false
namespace NCJ_ConstructorSuccessor
open Aeneas Aeneas.Std Result ControlFlow NCJ_ConstructorQM NCJ_ConstructorArrays

theorem source (z successor : Array Q 10#usize) (carry : Q)
    (hz : Holds Canon z) (hs : Holds Canon successor) (hc : Canon carry)
    (e : Usize) (bound : e.val≤10) :
    ∃ out,FIn_WeightsExtract.state_only_prefix.state_only_statement_points_loop
      (NCJ_Reverse.cursor e) z successor carry=ok out ∧ Holds Canon out := by
  let inv : (NCJ_Reverse.Rev × Array Q 10#usize × Q) → Prop := fun s=>
    s.1=NCJ_Reverse.cursor s.1.iter.end ∧ s.1.iter.end.val≤10 ∧ Holds Canon s.2.1 ∧ Canon s.2.2
  have spec : WP.spec (FIn_WeightsExtract.state_only_prefix.state_only_statement_points_loop
      (NCJ_Reverse.cursor e) z successor carry) (Holds Canon) := by
    unfold FIn_WeightsExtract.state_only_prefix.state_only_statement_points_loop
    apply loop.spec_decr_nat (fun s : NCJ_Reverse.Rev × Array Q 10#usize × Q=>s.1.iter.end.val)
      inv (Holds Canon)
      (fun s=>FIn_WeightsExtract.state_only_prefix.state_only_statement_points_loop.body z s.1 s.2.1 s.2.2)
      (NCJ_Reverse.cursor e,successor,carry)
    · rintro ⟨iter,arr,carry⟩ ⟨cursor,cap,ca,cc⟩
      change iter=NCJ_Reverse.cursor iter.iter.end at cursor
      change iter.iter.end.val≤10 at cap
      change Holds Canon arr at ca
      change Canon carry at cc
      by_cases zero : iter.iter.end.val=0
      · have ez : iter.iter.end=0#usize := UScalar.eq_of_val_eq zero
        have it : iter=NCJ_Reverse.cursor 0#usize := cursor.trans (congrArg NCJ_Reverse.cursor ez)
        have stopped := NCJ_Reverse.stop
        unfold NCJ_Reverse.next at stopped
        simp only [FIn_WeightsExtract.state_only_prefix.state_only_statement_points_loop.body,it,stopped,bind_tc_ok]
        dsimp! only
        rw [WP.spec_ok]
        exact ca
      · obtain ⟨j,dec,advance⟩ := NCJ_Reverse.step iter.iter.end (by omega)
        have next : NCJ_Reverse.next iter=ok (some j,NCJ_Reverse.cursor j) := by rw [cursor];exact advance
        obtain ⟨out,nextCarry,body,co,cn⟩ := NCJ_ConstructorSuccessorCell.source z arr carry hz ca cc
          iter (NCJ_Reverse.cursor j) j (by omega) next
        rw [body,WP.spec_ok]
        change (NCJ_Reverse.cursor j=NCJ_Reverse.cursor j ∧ j.val≤10 ∧ Holds Canon out ∧ Canon nextCarry) ∧
          j.val< iter.iter.end.val
        exact ⟨⟨rfl,by omega,co,cn⟩,by omega⟩
    · exact ⟨rfl,bound,hs,hc⟩
  exact WP.spec_imp_exists spec

#print axioms source
end NCJ_ConstructorSuccessor
