import NJE_CountGroup
import NJE_CountArithmetic

set_option autoImplicit false
namespace NJE_CountRow
open Aeneas Aeneas.Std Result ControlFlow NJA_Multiproof
open AspisR1.MultiproofConeCountPhysical

theorem step (a : Array U32 16#usize) (n i w c : Usize) (hn : n.val≤16)
    (active : i<n) (safe : w.val≤ i.val)
    (sorted : (unread (NJA_CountDrop.keys a) n.val i.val).Pairwise (·<·)) :
    let p := U32.wrapping_shr (a.val[i.val]'(by have h : a.val.length=16 := a.property;scalar_tac)) 1#u32
    ∃ q : Usize,
      (q.val=AspisR1.MultiproofConeLiveOrder.advance (NJA_CountDrop.keys a) n.val i.val) ∧
      (i.val+1≤q.val) ∧ (q.val≤n.val) ∧ (q.val ≤ i.val+2) ∧
      multiproof.node_count_loop0_loop0.body .Two n a c w i=
        ok (cont (a.set w p,
          Usize.wrapping_add c (Usize.wrapping_sub 2#usize (Usize.wrapping_sub q i)),
          Usize.wrapping_add w 1#usize,q)) := by
 dsimp only
 have ib : i.val<(16#usize).val := by scalar_tac
 have wb : w.val<16 := by scalar_tac
 obtain ⟨q,hq,eq,lower,upper,delta⟩ := NJE_CountGroup.total a n i hn (by scalar_tac) sorted
 refine ⟨q,eq,lower,upper,delta,?_⟩
 unfold multiproof.node_count_loop0_loop0.body
 rw [if_pos active,NJA_Arity.index_result,NJA_Reads.index_ok a i ib]
 simp only [NJA_Arity.two_bits,bind_tc_ok,lift]
 rw [hq,NJA_Arity.two_width]
 simp only [bind_tc_ok,lift]
 rw [NJE_CountArithmetic.update_result a w _ wb]
 rfl

theorem exit (a : Array U32 16#usize) (n i w c : Usize) (done : ¬i<n) :
    multiproof.node_count_loop0_loop0.body .Two n a c w i=ok (ControlFlow.done (a,c,w)) := by
 simp only [multiproof.node_count_loop0_loop0.body,if_neg done]

#print step
#print axioms step
#print exit
#print axioms exit
end NJE_CountRow
