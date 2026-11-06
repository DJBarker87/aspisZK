import NJA_CountDrop
import MultiproofConeCountGroups

set_option autoImplicit false
namespace NJA_CountSorted
open Aeneas Aeneas.Std Result NJA_Multiproof
open AspisR1 OraclePortFrozenOrder MultiproofConeCountPhysical
attribute [local instance] Classical.propDecidable

theorem group (a : Array U32 16#usize) (n j : Usize) (hn : n.val≤16)
 (active : j.val<n.val) (rest : List Nat)
 (head : unread (NJA_CountDrop.keys a) n.val j.val = NJA_CountDrop.keys a j.val::rest)
 (sorted : (NJA_CountDrop.keys a j.val::rest).Pairwise (·<·)) :
 ∃ q : Usize,
 multiproof.node_count_loop0_loop0_loop0 .Two a n
   (U32.wrapping_shr (a.val[j.val]'(by have h:a.val.length=16:=a.property;omega)) 1#u32) j = ok q ∧
 j.val≤q.val ∧ q.val≤n.val ∧
 unread (NJA_CountDrop.keys a) n.val q.val =
   if (match rest with | x::_ => decide (paired (NJA_CountDrop.keys a j.val) x) | [] => false)
   then rest.drop 1 else rest := by
 let p := U32.wrapping_shr (a.val[j.val]'(by have h:a.val.length=16:=a.property;omega)) 1#u32
 obtain ⟨q,hq,lower,upper,tail⟩ := NJA_CountDrop.total a n p hn (n.val-j.val) j (by omega) (by omega)
 refine ⟨q,hq,lower,upper,?_⟩
 rw [tail,head]
 have value : p.val = NJA_CountDrop.keys a j.val/2 := by
   rw [NJA_CountDrop.read a j (by omega)]
   exact NJA_CountStep.shift_one _
 rw [value]
 exact MultiproofConeCountGroups.drop_group _ rest sorted

#print axioms group
end NJA_CountSorted
