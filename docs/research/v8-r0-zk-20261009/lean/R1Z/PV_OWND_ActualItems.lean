import R1Z.PV_OWND_ActualHeader
set_option autoImplicit false
namespace R1Z.PV_OWND_ActualItems
open PV_OWN_Heap PV_OWNC_Vector PV_OWN_Link PV_OWN_Bytes

def items (b : Buffer Link) : List Link := (List.range b.length).map b.values

theorem source (m : Memory) (t : Token) (owner : Nat) (payload : Nat → Link → Bytes) :
 items (PV_OWND_ActualBytes.initialized m t owner payload)=PV_OWND_LegacySource.links := by
 apply List.ext_getElem
 · simp only [items,List.length_map,List.length_range,PV_OWND_ActualHeader.length,PV_OWND_LegacyCount.count]
 · intro i hi hj
   simp only [items,List.getElem_map,List.getElem_range]
   exact PV_OWND_ActualHeader.values m t owner i payload hj
#print axioms source
end R1Z.PV_OWND_ActualItems
