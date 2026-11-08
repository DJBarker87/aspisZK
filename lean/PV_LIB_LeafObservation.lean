import PV_LIB_Observation
import PV_W1_ClosedLeaves
set_option autoImplicit false
namespace PV_LIB
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_EVHB_OwnerMachine

def leafObserve {E : Type} (q : Store Data × Reply OWNER E Data) :
    Observation (Answer Data) (Store Data × OWNER) E :=
  match q.2.answer with
  | .fault .abort => .abort q.2.events
  | _ => .returned q.2.answer (storeView q.1,q.2.world) q.2.events

theorem leaf_abort_prefix {E : Type} (s : Store Data) (w : OWNER) (es : List E) :
    leafObserve (s,(⟨.fault .abort,w,es⟩ : Reply OWNER E Data)) =
      Observation.abort es := rfl

#print axioms leaf_abort_prefix
end PV_LIB
