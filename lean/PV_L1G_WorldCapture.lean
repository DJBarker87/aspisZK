import R1Z.PV_W_Threading
import PV_RJ4IDB_Channels
set_option autoImplicit false
namespace PV_L1G_WorldCapture
open R1Z.PV_W_Threading
variable {W C E A B : Type}
/-- Auxiliary projection of an independently retained source Run. The encoder
must still be bound to each deployed leaf; this is no native event decoder. -/
def word (encode : W × C → List PV_RJ4IDB.Event) (r : Run W C E A) := r.calls.flatMap encode

theorem bind_ok (encode : W × C → List PV_RJ4IDB.Event)
 (m : M W C E A) (k : A → M W C E B) (w : W) (a : A)
 (h : (m w).outcome = .ok a) :
 word encode (R1Z.PV_W_Threading.bind m k w) =
 word encode (m w) ++ word encode (k a (m w).world) := by
 rw [R1Z.PV_W_Threading.bind_ok m k w a h]
 exact List.flatMap_append
#print axioms bind_ok

theorem bind_fail (encode : W × C → List PV_RJ4IDB.Event)
 (m : M W C E A) (k : A → M W C E B) (w : W) (e : E)
 (h : (m w).outcome = .fail e) :
 word encode (R1Z.PV_W_Threading.bind m k w) = word encode (m w) := by
 rw [R1Z.PV_W_Threading.bind_fail m k w e h]
#print axioms bind_fail

theorem bind_div (encode : W × C → List PV_RJ4IDB.Event)
 (m : M W C E A) (k : A → M W C E B) (w : W)
 (h : (m w).outcome = .div) :
 word encode (R1Z.PV_W_Threading.bind m k w) = word encode (m w) := by
 rw [R1Z.PV_W_Threading.bind_div m k w h]
#print axioms bind_div
end PV_L1G_WorldCapture
