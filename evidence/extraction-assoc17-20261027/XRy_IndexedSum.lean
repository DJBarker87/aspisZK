import XRy_ClaimPartFactor
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers XRy_ClaimSumStep
set_option autoImplicit false
namespace XRy_IndexedSum

theorem run_fold (n : Nat) (k parts : Seven) (i : Usize) (sum : C.E)
 (bound : i.val+n≤7) :
 XRy_ClaimSumLoop.run k parts n i sum =
 (List.range' i.val n).foldlM (fun sum j => step k parts sum (XRn_Join_usize j)) sum := by
 induction n generalizing i sum with
 | zero => rfl
 | succ n ih =>
   have hi : i.val<7 := by omega
   have hAdd : (i+1#usize : Result Usize) ⦃ j => j.val=i.val+1 ⦄ := by
     apply UScalar.add_spec
     scalar_tac
   obtain ⟨j,ej,hj⟩ := WP.spec_imp_exists hAdd
   simp only [XRy_ClaimSumLoop.run,List.range'_succ,List.foldlM_cons,
     XRy_ArrayRead.usize_small i hi]
   apply (bind_eq_iff _ _ _).mpr
   intro next hnext
   rw [ej,bind_tc_ok]
   have ht := ih j next (by omega)
   simpa only [hj] using ht

#print axioms run_fold
end XRy_IndexedSum
