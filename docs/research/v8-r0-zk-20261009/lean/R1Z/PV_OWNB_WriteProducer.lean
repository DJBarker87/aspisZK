import R1Z.PV_OWNB_LinkCodec
set_option autoImplicit false
namespace R1Z.PV_OWNB_WriteProducer
open PV_OWN_Heap PV_OWN_Bytes PV_OWN_Link PV_OWNB_LinkCodec
/-- A field assignment preserves all other active bytes and arbitrary padding. -/
theorem write (c : Cell) (s : Nat) (v : Link) (p : UInt16) (h:NativeView c s v) :
 NativeView (store c s 2 (PV_OWN_U16.encode p)) s {v with producer:=p} := by
 refine ⟨h.1,?_⟩
 intro i b hi
 by_cases small:i<2
 · have hh:PV_OWN_U16.encode p i=some b := (PV_OWNB_LinkBytes.producer _ i small).symm.trans hi
   change overwrite c.contents s 2 (PV_OWN_U16.encode p) (s+i)=some b
   rw [inside _ _ _ _ _ small]
   exact hh
 · have unchanged:PV_OWNB_LinkBytes.encode {v with producer:=p} i=PV_OWNB_LinkBytes.encode v i := by
    simp [PV_OWNB_LinkBytes.encode,small]
   change overwrite c.contents s 2 (PV_OWN_U16.encode p) (s+i)=some b
   rw [outside _ _ _ _ _ (by right; omega)]
   exact h.2 i b (unchanged.symm.trans hi)
#print axioms write
end R1Z.PV_OWNB_WriteProducer
