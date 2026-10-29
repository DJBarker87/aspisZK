import R1Z.PV_OWNB_LinkCodec
set_option autoImplicit false
namespace R1Z.PV_OWNB_WriteConsumer
open PV_OWN_Heap PV_OWN_Bytes PV_OWN_Link PV_OWNB_LinkCodec
theorem write (c : Cell) (s : Nat) (v : Link) (p : UInt16) (h:NativeView c s v) :
 NativeView (store c (s+2) 2 (PV_OWN_U16.encode p)) s {v with consumer:=p} := by
 refine ⟨h.1,?_⟩
 intro i b hi
 by_cases active:2≤i ∧ i<4
 · have ii:i=2+(i-2) := by omega
   have hh:PV_OWN_U16.encode p (i-2)=some b := by
    rw [ii,PV_OWNB_LinkBytes.consumer _ (i-2) (by omega)] at hi
    exact hi
   change overwrite c.contents (s+2) 2 (PV_OWN_U16.encode p) (s+i)=some b
   have off:s+i=(s+2)+(i-2) := by omega
   rw [off,inside _ _ _ _ _ (by omega)]
   exact hh
 · have unchanged:PV_OWNB_LinkBytes.encode {v with consumer:=p} i=PV_OWNB_LinkBytes.encode v i := by
    by_cases small:i<2
    · simp [PV_OWNB_LinkBytes.encode,small]
    · have big:¬i<4 := by omega
      simp [PV_OWNB_LinkBytes.encode,small,big]
   change overwrite c.contents (s+2) 2 (PV_OWN_U16.encode p) (s+i)=some b
   rw [outside _ _ _ _ _ (by omega)]
   exact h.2 i b (unchanged.symm.trans hi)
#print axioms write
end R1Z.PV_OWNB_WriteConsumer
