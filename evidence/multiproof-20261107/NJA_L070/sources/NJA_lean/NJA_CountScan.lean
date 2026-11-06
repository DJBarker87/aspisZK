import NJA_CountStep

set_option autoImplicit false
namespace NJA_CountScan
open Aeneas Aeneas.Std Result ControlFlow NJA_Multiproof

-- Symbolic bounded induction over the unchanged emitted inner loop.
-- No sortedness or endpoint-success hypothesis is required.
theorem total (a : Array U32 16#usize) (n : Usize) (p : U32)
 (hn : n.val≤16) (fuel : Nat) (j : Usize) (hj : j.val≤n.val)
 (hf : n.val-j.val≤fuel) :
 ∃ q : Usize, multiproof.node_count_loop0_loop0_loop0 .Two a n p j = ok q ∧
 j.val≤q.val ∧ q.val≤n.val := by
 induction fuel generalizing j with
 | zero =>
   have exit : ¬j<n := by scalar_tac
   refine ⟨j,?_,by omega,by omega⟩
   rw [multiproof.node_count_loop0_loop0_loop0,loop.eq_def,NJA_CountStep.group_step a n j p hn]
   simp [exit]
 | succ fuel ih =>
   by_cases active : j<n
   · have jb : j.val<16 := by scalar_tac
     have adv := NJA_CountStep.advance j jb
     by_cases same : (a.val[j.val]'(by have len : a.val.length=16:=a.property;scalar_tac)).val/2=p.val
     · obtain ⟨q,hq,lower,upper⟩ := ih (Usize.wrapping_add j 1#usize) (by scalar_tac) (by scalar_tac)
       refine ⟨q,?_,by omega,upper⟩
       rw [multiproof.node_count_loop0_loop0_loop0,loop.eq_def,NJA_CountStep.group_step a n j p hn]
       simpa only [if_pos active,if_pos same] using hq
     · refine ⟨j,?_,by omega,hj⟩
       rw [multiproof.node_count_loop0_loop0_loop0,loop.eq_def,NJA_CountStep.group_step a n j p hn]
       simp [active,same]
   · refine ⟨j,?_,by omega,hj⟩
     rw [multiproof.node_count_loop0_loop0_loop0,loop.eq_def,NJA_CountStep.group_step a n j p hn]
     simp [active]

#print axioms total
end NJA_CountScan
