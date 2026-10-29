import PV_L1G_WorldCapture
set_option autoImplicit false
namespace PV_L1G_CountPrefixes
open R1Z.PV_W_Threading PV_RJ4IDB
open PV_L1G_WorldCapture (word)
variable {W C E A B : Type}
def channels (es : List Event) := (counts es,rejections es)
theorem append (a b : List Event) :
 channels (a++b) = (counts a++counts b,rejections a++rejections b) := by
 simp only [channels,counts,rejections,List.filterMap_append]
#print axioms append
theorem success (encode : W × C → List Event)
 (m : M W C E A) (k : A → M W C E B) (w : W) (a : A)
 (h : (m w).outcome = .ok a) :
 channels (word encode (R1Z.PV_W_Threading.bind m k w)) =
 (counts (word encode (m w)) ++ counts (word encode (k a (m w).world)),
  rejections (word encode (m w)) ++ rejections (word encode (k a (m w).world))) := by
 rw [PV_L1G_WorldCapture.bind_ok encode m k w a h,append]
#print axioms success
theorem failed (encode : W × C → List Event)
 (m : M W C E A) (k : A → M W C E B) (w : W) (e : E)
 (h : (m w).outcome = .fail e) :
 channels (word encode (R1Z.PV_W_Threading.bind m k w)) = channels (word encode (m w)) := by
 rw [PV_L1G_WorldCapture.bind_fail encode m k w e h]
#print axioms failed
theorem divergent (encode : W × C → List Event)
 (m : M W C E A) (k : A → M W C E B) (w : W)
 (h : (m w).outcome = .div) :
 channels (word encode (R1Z.PV_W_Threading.bind m k w)) = channels (word encode (m w)) := by
 rw [PV_L1G_WorldCapture.bind_div encode m k w h]
#print axioms divergent
end PV_L1G_CountPrefixes
