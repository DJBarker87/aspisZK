import NJE_CountRow
import NJE_CountKeyFrame
import NJE_CountRowBounds
import MultiproofConeCountPhysicalLevels

set_option autoImplicit false
namespace NJE_CountRows
open Aeneas Aeneas.Std Result ControlFlow NJA_Multiproof
open AspisR1 MultiproofConeCountPhysical MultiproofConeLiveOrder
attribute [local instance] Classical.propDecidable

theorem total (fuel : Nat) (a : Array U32 16#usize) (n i w c : Usize)
    (hn : n.val≤16) (safe : w.val ≤ i.val) (end_bound : i.val≤n.val)
    (sorted : (unread (NJA_CountDrop.keys a) n.val i.val).Pairwise (·<·))
    (range : ∀ x∈unread (NJA_CountDrop.keys a) n.val i.val, x<262144)
    (budget : c.val+(n.val-i.val)≤576) (enough : n.val-i.val≤fuel) :
    ∃ (b : Array U32 16#usize) (d v : Usize),
      multiproof.node_count_loop0_loop0 .Two a n c w i=ok (b,d,v) ∧
      v.val≤n.val ∧ d.val≤c.val+(n.val-i.val) ∧
      cells (NJA_CountDrop.keys b) 0 v.val=
        (rows fuel (NJA_CountDrop.keys a) n.val i.val w.val c.val).1 ∧
      d.val=(rows fuel (NJA_CountDrop.keys a) n.val i.val w.val c.val).2 := by
 induction fuel generalizing a i w c with
 | zero =>
   have inactive : ¬i<n := by scalar_tac
   refine ⟨a,c,w,?_,by omega,by omega,rfl,rfl⟩
   rw [multiproof.node_count_loop0_loop0,loop.eq_def]
   dsimp only
   rw [NJE_CountRow.exit a n i w c inactive]
   rfl
 | succ fuel ih =>
   by_cases active : i<n
   · have nat_active : i.val<n.val := by scalar_tac
     have ib : i.val<16 := by omega
     have wb : w.val<16 := by omega
     obtain ⟨q,qvalue,lower,upper,delta,body⟩ := NJE_CountRow.step a n i w c hn active safe sorted
     let p := U32.wrapping_shr (a.val[i.val]'(by have h:a.val.length=16:=a.property;omega)) 1#u32
     let a1 := a.set w p
     let c1 := Usize.wrapping_add c (Usize.wrapping_sub 2#usize (Usize.wrapping_sub q i))
     let w1 := Usize.wrapping_add w 1#usize
     have body' : multiproof.node_count_loop0_loop0.body .Two n a c w i=
         ok (cont (a1,c1,w1,q)) := body
     have parent : p=U32.wrapping_shr (a.val[i.val]!) 1#u32 := by
       rw [getElem!_pos a.val i.val (by have h:a.val.length=16:=a.property;omega)]
     have keys : NJA_CountDrop.keys a1=write (NJA_CountDrop.keys a) i.val w.val := by
       dsimp only [a1]
       rw [parent]
       exact NJE_CountKeyFrame.whole a i w ib wb
     have wvalue : w1.val=w.val+1 := NJA_CountStep.advance w wb
     have cvalue : c1.val=c.val+(if pairAt (NJA_CountDrop.keys a) n.val i.val then 0 else 1) := by
       have h := NJE_CountRowBounds.count_value (NJA_CountDrop.keys a) n.val c i q (by omega) qvalue
       by_cases paired : pairAt (NJA_CountDrop.keys a) n.val i.val <;>
         simpa [c1,NJE_CountRowBounds.cost,paired] using h
     have progress := NJE_CountRowBounds.progress (NJA_CountDrop.keys a) n.val i.val
     rw [←qvalue] at progress
     have growth : c1.val+(n.val-q.val)≤c.val+(n.val-i.val) := by
       by_cases paired : pairAt (NJA_CountDrop.keys a) n.val i.val <;>
         simp [NJE_CountRowBounds.cost,paired] at progress cvalue <;> omega
     have domains := MultiproofConeCountPhysicalLevels.unread_domain (NJA_CountDrop.keys a)
       n.val i.val w.val safe nat_active sorted range
     have next_sorted : (unread (NJA_CountDrop.keys a1) n.val q.val).Pairwise (·<·) := by
       rw [keys,qvalue]
       exact domains.1
     have next_range : ∀ x∈unread (NJA_CountDrop.keys a1) n.val q.val, x<262144 := by
       rw [keys,qvalue]
       exact domains.2
     obtain ⟨b,d,v,exec,vb,db,prefix_eq,count_eq⟩ := ih a1 q w1 c1
       (by omega) upper next_sorted next_range (by omega) (by omega)
     have model_step : rows (fuel+1) (NJA_CountDrop.keys a) n.val i.val w.val c.val=
         rows fuel (NJA_CountDrop.keys a1) n.val q.val w1.val c1.val := by
       rw [rows,if_pos nat_active,←keys,←qvalue,←wvalue,←cvalue]
     refine ⟨b,d,v,?_,vb,by omega,?_,?_⟩
     · rw [multiproof.node_count_loop0_loop0,loop.eq_def]
       dsimp only
       rw [body']
       simpa only [multiproof.node_count_loop0_loop0] using exec
     · rw [model_step]
       exact prefix_eq
     · rw [model_step]
       exact count_eq
   · have nat_inactive : ¬i.val<n.val := by scalar_tac
     refine ⟨a,c,w,?_,by omega,by omega,?_,?_⟩
     · rw [multiproof.node_count_loop0_loop0,loop.eq_def]
       dsimp only
       rw [NJE_CountRow.exit a n i w c active]
       rfl
     · rw [rows,if_neg nat_inactive]
     · rw [rows,if_neg nat_inactive]

#print total
#print axioms total
end NJE_CountRows
