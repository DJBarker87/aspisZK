import NJA_CountScan
import MultiproofConeCountPhysical

set_option autoImplicit false
namespace NJA_CountDrop
open Aeneas Aeneas.Std Result ControlFlow NJA_Multiproof
open AspisR1.MultiproofConeCountPhysical

def keys (a : Array U32 16#usize) (i : Nat) : Nat := (a.val[i]!).val

theorem read (a : Array U32 16#usize) (j : Usize) (hj : j.val<16) :
 keys a j.val = (a.val[j.val]'(by have h : a.val.length=16:=a.property;omega)).val := by
 unfold keys
 rw [getElem!_pos a.val j.val (by have h : a.val.length=16:=a.property;omega)]

theorem total (a : Array U32 16#usize) (n : Usize) (p : U32)
 (hn : n.val≤16) (fuel : Nat) (j : Usize) (hj : j.val≤n.val)
 (hf : n.val-j.val≤fuel) :
 ∃ q : Usize, multiproof.node_count_loop0_loop0_loop0 .Two a n p j = ok q ∧
 j.val≤q.val ∧ q.val≤n.val ∧
 unread (keys a) n.val q.val =
   (unread (keys a) n.val j.val).dropWhile (fun x => decide (x/2=p.val)) := by
 induction fuel generalizing j with
 | zero =>
   have eq : j.val=n.val := by omega
   have exit : ¬j<n := by scalar_tac
   refine ⟨j,?_,by omega,hj,?_⟩
   · rw [multiproof.node_count_loop0_loop0_loop0,loop.eq_def,NJA_CountStep.group_step a n j p hn]
     simp [exit]
   · simp [unread,cells,eq]
 | succ fuel ih =>
   by_cases active : j<n
   · have jb : j.val<16 := by scalar_tac
     have adv := NJA_CountStep.advance j jb
     have cons := unread_cons (keys a) n.val j.val (by scalar_tac)
     by_cases same : (a.val[j.val]'(by have len : a.val.length=16:=a.property;scalar_tac)).val/2=p.val
     · obtain ⟨q,hq,lower,upper,tail⟩ := ih (Usize.wrapping_add j 1#usize) (by scalar_tac) (by scalar_tac)
       refine ⟨q,?_,by omega,upper,?_⟩
       · rw [multiproof.node_count_loop0_loop0_loop0,loop.eq_def,NJA_CountStep.group_step a n j p hn]
         simpa only [dif_pos active,if_pos active,if_pos same,multiproof.node_count_loop0_loop0_loop0] using hq
       · rw [cons,List.dropWhile_cons]
         simpa [read a j jb,same,adv] using tail
     · refine ⟨j,?_,by omega,hj,?_⟩
       · rw [multiproof.node_count_loop0_loop0_loop0,loop.eq_def,NJA_CountStep.group_step a n j p hn]
         simp [active,same]
       · rw [cons,List.dropWhile_cons]
         simp [read a j jb,same]
   · have eq : j.val=n.val := by scalar_tac
     refine ⟨j,?_,by omega,hj,?_⟩
     · rw [multiproof.node_count_loop0_loop0_loop0,loop.eq_def,NJA_CountStep.group_step a n j p hn]
       simp [active]
     · simp [unread,cells,eq]

#print axioms read
#print axioms total
end NJA_CountDrop
