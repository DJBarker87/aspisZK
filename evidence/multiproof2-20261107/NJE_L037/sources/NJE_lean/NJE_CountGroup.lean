import NJA_CountSorted

set_option autoImplicit false
namespace NJE_CountGroup
open Aeneas Aeneas.Std Result NJA_Multiproof
open AspisR1 OraclePortFrozenOrder MultiproofConeCountPhysical
attribute [local instance] Classical.propDecidable

theorem total (a : Array U32 16#usize) (n i : Usize) (hn : n.val≤16)
    (active : i.val<n.val)
    (sorted : (unread (NJA_CountDrop.keys a) n.val i.val).Pairwise (·<·)) :
    ∃ q : Usize,
      multiproof.node_count_loop0_loop0_loop0 .Two a n
        (U32.wrapping_shr (a.val[i.val]'(by have h : a.val.length=16 := a.property;omega)) 1#u32) i=ok q ∧
      q.val=MultiproofConeLiveOrder.advance (NJA_CountDrop.keys a) n.val i.val ∧
      (i.val + 1 ≤ q.val) ∧ (q.val ≤ n.val) ∧ (q.val ≤ i.val + 2) := by
 let k := NJA_CountDrop.keys a
 have head := unread_cons k n.val i.val active
 have sorted' : (k i.val::unread k n.val (i.val+1)).Pairwise (·<·) := by
   change (unread k n.val i.val).Pairwise (·<·) at sorted
   rwa [head] at sorted
 obtain ⟨q,hq,lower,upper,tail⟩ := NJA_CountSorted.group a n i hn active
   (unread k n.val (i.val+1)) head sorted'
 have group := group_tail k n.val i.val active
 change unread k n.val q.val =
   (if (match unread k n.val (i.val+1) with | x::_ => decide (paired (k i.val) x) | [] => false)
    then (unread k n.val (i.val+1)).drop 1 else unread k n.val (i.val+1)) at tail
 rw [group.1] at tail
 have same := tail.trans group.2
 have lengths := congrArg List.length same
 simp only [unread,cells,List.length_map,List.length_range] at lengths
 have adv := advance_bounds k n.val i.val active
 have eq : q.val=MultiproofConeLiveOrder.advance k n.val i.val := by omega
 refine ⟨q,hq,eq,by omega,upper,?_⟩
 rw [eq]
 unfold MultiproofConeLiveOrder.advance
 split <;> omega

#print total
#print axioms total
end NJE_CountGroup
