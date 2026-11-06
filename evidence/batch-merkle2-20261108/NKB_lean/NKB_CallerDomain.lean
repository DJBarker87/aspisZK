import NKB_IndexFold
import NJV_WellInput

set_option autoImplicit false
namespace NKB_CallerDomain
open Aeneas Aeneas.Std Result MultiproofConeRef AspisR1
open OraclePortFrozenOrder

/-- General counted caller domain: unlike NJV_UnitDomain.Domain this does not
retain the <=10 unit restriction into the twelve-query transaction. -/
theorem well (s : reference.Scratch) (positive : 0<s.n.val) (size : s.n.val≤12)
    (ordered : MultiproofConeLiveOrder.Strict (MultiproofConeLivePreservation.keys s) 0 s.n.val)
    (canonical : ∀ j,j<s.n.val → MultiproofConeLivePreservation.keys s j<262144) :
 wellFormed (NJV_UnitDomain.keys s) := by
 have sorted := MultiproofConePhysicalViews.live_sorted s s.n.val ordered
 have bounds : ∀ x∈NJV_UnitDomain.keys s,x<262144 := by
   simpa only [NJV_UnitDomain.keys,MultiproofConePhysicalViews.live,
     MultiproofConePhysicalLive.view,List.map_map,Function.comp_def,
     MultiproofConePhysicalViews.decodeEntry,MultiproofConePhysicalLive.cell,
     Nat.zero_add,List.forall_mem_map,List.mem_range,
     MultiproofConeLivePreservation.keys] using canonical

 change NJV_UnitDomain.keys s≠[] ∧
   (NJV_UnitDomain.keys s).length≤16 ∧
   (NJV_UnitDomain.keys s).Pairwise (·<·) ∧
   (∀ i∈NJV_UnitDomain.keys s,i<262144)
 have nonempty : NJV_UnitDomain.keys s≠[] := by
   intro empty
   have len := congrArg List.length empty
   rw [NJV_UnitDomain.key_length] at len
   simp only [List.length_nil] at len
   omega
 exact ⟨nonempty,by rw [NJV_UnitDomain.key_length];omega,sorted,bounds⟩

#print axioms well
end NKB_CallerDomain
