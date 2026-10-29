import R1Z.PV_OWNC_PushOwned
set_option autoImplicit false
namespace R1Z.PV_OWNC_PushValid
open PV_OWNC_Vector PV_OWN_View

theorem valid {T : Type} (k : Codec T) (b : Buffer T) (v : T)
 (actual : PV_OWN_Bytes.Bytes) (h:Valid k b) (room:b.length<b.capacity)
 (bounded:∀ x i z, k.encode x i=some z → i<k.width)
 (bytes:PV_OWNB_Padding.Agrees (k.encode v) actual) : Valid k (push k b v actual) := by
 have own:=PV_OWNC_PushOwned.writable k b v actual h
 have new:=PV_OWNC_PushBytes.initialized k b v actual h room (bounded v) bytes
 have old:=PV_OWNC_PushBytes.prefix k b v actual h bounded
 unfold Valid at h ⊢
 refine ⟨own,h.2.1,h.2.2.1,?_,?_⟩
 · change b.length+1≤b.capacity
   omega
 · intro i hi
   change i<b.length+1 at hi
   by_cases eq:i=b.length
   · subst i
     simpa only [push,ite_true] using new
   · have lt:i<b.length := by omega
     simpa only [push,eq,ite_false] using old i lt
#print axioms valid
end R1Z.PV_OWNC_PushValid
