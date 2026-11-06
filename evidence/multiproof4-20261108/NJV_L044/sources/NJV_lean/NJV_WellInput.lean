import NJV_UnitDomain
import NJE_WellFrozen

set_option autoImplicit false
noncomputable section
namespace NJV_WellInput
open Aeneas Aeneas.Std Result NJP_DigestCarrier NJP_ScratchCarrier
open MultiproofConeRef
open AspisR1.MultiproofConePhysicalViews AspisR1.MultiproofConePhysicalLive
open AspisR1.OraclePortFrozenOrder
attribute [local instance] Classical.propDecidable

/-- Exact SAME borrowed prefix seen by the native well_formed call. -/
theorem keys (s : reference.Scratch) (bound : s.n.val≤16) :
 NJV_UnitDomain.keys s=(s.idx.val.take s.n.val).map (fun x : U32 => x.val) := by
 have len : s.idx.val.length=16 := s.idx.property
 apply List.ext_getElem
 · simp only [NJV_UnitDomain.key_length,List.length_map,List.length_take,len,Nat.min_eq_left bound]
 · intro j hj hj'
   have jb : j<s.n.val := by simpa only [NJV_UnitDomain.key_length] using hj
   have arr : j<s.idx.val.length := by omega
   simp only [NJV_UnitDomain.keys,live,view,List.map_map,List.getElem_map,List.getElem_range,
     Function.comp_apply,decodeEntry,cell,Nat.zero_add,List.getElem_take,getElem!_pos _ j arr]

/-- CLOSED well_formed complete reply installed at that exact input, internally.
The parent has no free well-formedness Bool or successful-child equation. -/
theorem reply (s : reference.Scratch) (bound : s.n.val≤16) :
 NJE_WellFrozen.emitted ⟨s.idx.val.take s.n.val,by
   have cap := (Array.to_slice s.idx).property
   change s.idx.val.length≤Usize.max at cap
   simp only [List.length_take]
   omega⟩=
 ok (decide (wellFormed (NJV_UnitDomain.keys s))) := by
 rw [NJE_WellFrozen.association,NJE_WellSource.source,NJA_WellFormed.source_eq,keys s bound]

#print keys
#print axioms keys
#print reply
#print axioms reply
end NJV_WellInput
end
