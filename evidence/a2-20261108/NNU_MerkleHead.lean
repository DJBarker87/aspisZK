import NNU_MerkleValidity
set_option autoImplicit false
namespace AspisR1.NNU_MerkleHead
open Aeneas Aeneas.Std Result MultiproofConeRef
open MultiproofConePhysicalViews MultiproofConeLivePreservation

theorem source (s : reference.Scratch)
 (guard : OraclePortFrozenOrder.wellFormed ((live s 0 s.n.val).map Prod.fst)) :
 0 < s.n.val ∧ s.n.val≤16 ∧ reference.valid_indices s.idx s.n 0#usize=.ok true := by
 have len : ((live s 0 s.n.val).map Prod.fst).length=s.n.val := by
   simp only [List.length_map,MultiproofConeRootGuard.live_length]
 have positive : 0 < s.n.val := by
   by_contra bad
   have empty : (live s 0 s.n.val).map Prod.fst=[] := List.length_eq_zero_iff.mp (by omega)
   exact guard.1 empty
 have bound : s.n.val≤16 := by have := guard.2.1; omega
 have canonical : ∀ j, j < s.n.val → s.idx.val[j]!.val < 262144 := by
   intro j hj
   apply guard.2.2.2
   apply List.mem_iff_getElem.mpr
   refine ⟨j,by omega,?_⟩
   simp only [live,MultiproofConePhysicalLive.view,List.map_map,List.getElem_map,
    List.getElem_range,Function.comp_apply,decodeEntry,MultiproofConePhysicalLive.cell,Nat.zero_add]
 have ordered : ∀ a b, a < b → b < s.n.val → s.idx.val[a]!.val < s.idx.val[b]!.val := by
   intro a b ab bn
   exact MultiproofConePhysicalVerify.strict_of_live s guard.2.2.1 a b (Nat.zero_le _) ab bn
 refine ⟨positive,bound,?_⟩
 exact NNU_MerkleValidity.indices s.idx s.n bound canonical ordered s.n.val 0#usize (by simp)
#print axioms source
end AspisR1.NNU_MerkleHead
