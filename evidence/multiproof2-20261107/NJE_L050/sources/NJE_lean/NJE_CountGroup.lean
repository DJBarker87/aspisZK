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
 have head := unread_cons (NJA_CountDrop.keys a) n.val i.val active
 have sorted' : ((NJA_CountDrop.keys a) i.val::unread (NJA_CountDrop.keys a) n.val (i.val+1)).Pairwise (·<·) := by
   change (unread (NJA_CountDrop.keys a) n.val i.val).Pairwise (·<·) at sorted
   rwa [head] at sorted
 obtain ⟨q,hq,lower,upper,tail⟩ := NJA_CountSorted.group a n i hn active
   (unread (NJA_CountDrop.keys a) n.val (i.val+1)) head sorted'
 have rest_length : (unread (NJA_CountDrop.keys a) n.val (i.val+1)).length=n.val-(i.val+1) := by
   simp only [unread,cells,List.length_map,List.length_range]
 have eq : q.val=MultiproofConeLiveOrder.advance (NJA_CountDrop.keys a) n.val i.val := by
   cases rest_eq : unread (NJA_CountDrop.keys a) n.val (i.val+1) with
   | nil =>
     simp only [rest_eq,List.length_nil] at rest_length
     simp [rest_eq] at tail
     have lengths := congrArg List.length tail
     simp only [unread,cells,List.length_map,List.length_range,List.length_nil] at lengths
     have noPair : ¬MultiproofConeLiveOrder.pairAt (NJA_CountDrop.keys a) n.val i.val := by
       intro h
       have next := h.1
       omega
     simp only [MultiproofConeLiveOrder.advance,if_neg noPair]
     omega
   | cons x xs =>
     simp only [rest_eq,List.length_cons] at rest_length
     have next : i.val+1<n.val := by omega
     have heads := unread_cons (NJA_CountDrop.keys a) n.val (i.val+1) next
     have xeq : x=(NJA_CountDrop.keys a) (i.val+1) := (List.cons.inj (rest_eq.symm.trans heads)).1
     by_cases both : paired ((NJA_CountDrop.keys a) i.val) x
     · simp [rest_eq,both] at tail
       have lengths := congrArg List.length tail
       simp only [unread,cells,List.length_map,List.length_range] at lengths
       have hp : MultiproofConeLiveOrder.pairAt (NJA_CountDrop.keys a) n.val i.val := ⟨next,by simpa only [xeq] using both⟩
       simp only [MultiproofConeLiveOrder.advance,if_pos hp]
       omega
     · simp [rest_eq,both] at tail
       have lengths := congrArg List.length tail
       simp only [unread,cells,List.length_map,List.length_range,List.length_cons] at lengths
       have hp : ¬MultiproofConeLiveOrder.pairAt (NJA_CountDrop.keys a) n.val i.val := by
         intro hp
         exact both (by simpa only [xeq] using hp.2)
       simp only [MultiproofConeLiveOrder.advance,if_neg hp]
       omega
 have adv := advance_bounds (NJA_CountDrop.keys a) n.val i.val active
 refine ⟨q,hq,eq,by omega,upper,?_⟩
 rw [eq]
 unfold MultiproofConeLiveOrder.advance
 split <;> omega

#print total
#print axioms total
end NJE_CountGroup
