import PV_W1_NativeLeaves
import PV_FN_THREAD_OwnerWellFormed
import PV_FN_THREAD_f166SpawnCall
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_W3CalleeContracts
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
/-- Saved call-entry data comes from the operand evaluator's actual final
store. Its argument-reachable changes are kept explicitly on every reply. -/
def entry (c : Config) (t : Store Data) (rest : List PV_STX2_SliceSyntax.Node)
    (dest : Nat) (stack : List Config) : PV_W1_LeafBoundary.Entry :=
  ⟨t,c.frame.activation,c.callers,c.frame.loops,rest,.null,[],dest,stack⟩
theorem invariant (w : OWNER) (n : Nat)
    (pre : PV_FN_THREAD_OwnerWellFormed.OwnerWellFormed w n) :
    PV_W1_OwnerWellFormed.OwnerWellFormed w n := ⟨pre.identities,pre.activations⟩
/-- Instantiate the CLOSED269 contract at the actual zero-argument7916 cut. -/
theorem builder269 {E : Type} (B : Carrier OWNER Data) (c : Config)
    (H : PV_W1_OwnerNativeFrame.Backend E) (w : OWNER) (es : List E)
    (stack : List Config) (changes : Address → Option Data)
    (pre : PV_FN_THREAD_OwnerWellFormed.OwnerWellFormed w c.store.nextActivation) :
    PV_W1_NativeLeaves.Post269 B (entry c c.store (PV_THR2_F166.live.body.drop 7) 4 stack)
      H w [] es changes :=
  PV_W1_NativeLeaves.f269 B _ H w [] es changes (invariant w _ pre)
/-- Instantiate CLOSED271 on the ACTUAL move3/move7 operand reply store.
The dependent continuation must use afterEffects; no native store is reset. -/
theorem expect271 {E : Type} (B : Carrier OWNER Data) (c : Config) (t : Store Data)
    (H : PV_W1_OwnerNativeFrame.Backend E) (w : OWNER) (es : List E)
    (stack : List Config) (vs : List Data) (changes : Address → Option Data)
    (_evaluated : operands B w c.frame.activation [.move (.local 3),.move (.local 7)] c.store = some (vs,t))
    (pre : PV_FN_THREAD_OwnerWellFormed.OwnerWellFormed w t.nextActivation) :
    PV_W1_NativeLeaves.Post271 B (entry c t (PV_THR2_F166.live.body.drop 21) 0 stack)
      H w vs es changes :=
  PV_W1_NativeLeaves.f271 B _ H w vs es changes (invariant w _ pre)
/-- CLOSED360 receives precisely the moved local16 and its explicit store. -/
theorem arc360 {E : Type} (B : Carrier OWNER Data) (c : Config) (t : Store Data)
    (H : PV_W1_OwnerNativeFrame.Backend E) (w : OWNER) (es : List E)
    (stack : List Config) (vs : List Data) (changes : Address → Option Data)
    (_evaluated : operands B w c.frame.activation [.move (.local 16)] c.store = some (vs,t))
    (pre : PV_FN_THREAD_OwnerWellFormed.OwnerWellFormed w t.nextActivation) :
    PV_W1_NativeLeaves.Post360 B (entry c t (PV_THR2_F270.live.body.drop 28) 15 stack)
      H w vs es changes :=
  PV_W1_NativeLeaves.f360 B _ H w vs es changes (invariant w _ pre)
/-- CLOSED279 is instantiated at10197; all argument-reachable effects remain. -/
theorem result279 {E : Type} (B : Carrier OWNER Data) (c : Config) (t : Store Data)
    (H : PV_W1_OwnerNativeFrame.Backend E) (w : OWNER) (es : List E)
    (stack : List Config) (vs : List Data) (changes : Address → Option Data)
    (_evaluated : operands B w c.frame.activation [.move (.local 10)] c.store = some (vs,t))
    (pre : PV_FN_THREAD_OwnerWellFormed.OwnerWellFormed w t.nextActivation) :
    PV_W1_NativeLeaves.Post279 B (entry c t (PV_THR2_F270.live.body.drop 43) 9 stack)
      H w vs es changes :=
  PV_W1_NativeLeaves.f279 B _ H w vs es changes (invariant w _ pre)
/-- CLOSED280 is instantiated in the source error branch at10233, retaining
its pending/failure cases and argument-reachable changes. -/
theorem error280 {E : Type} (B : Carrier OWNER Data) (c : Config) (t : Store Data)
    (H : PV_W1_OwnerNativeFrame.Backend E) (w : OWNER) (es : List E)
    (stack : List Config) (vs : List Data) (changes : Address → Option Data)
    (_evaluated : operands B w c.frame.activation [.move (.local 19)] c.store = some (vs,t))
    (pre : PV_FN_THREAD_OwnerWellFormed.OwnerWellFormed w t.nextActivation) :
    PV_W1_NativeLeaves.Post280 B (entry c t (PV_THR2_F270.block67.drop 5 ++ PV_THR2_F270.live.body.drop 45) 0 stack)
      H w vs es changes :=
  PV_W1_NativeLeaves.f280 B _ H w vs es changes (invariant w _ pre)
#print axioms invariant
#print axioms builder269
#print axioms expect271
#print axioms arc360
#print axioms result279
#print axioms error280
end PV_FN_THREAD_W3CalleeContracts
