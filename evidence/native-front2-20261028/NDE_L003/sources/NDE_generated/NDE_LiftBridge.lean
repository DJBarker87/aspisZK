import NDE_Reference.Funs
import RPu_FIq_CopyPrefix
import RPu_FIq_Native08
import RPu_FIq_Native04
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NDE_LiftBridge

def toNative (q : NDE_Reference.Q) : FIq_Native.field.QM31 :=
  ⟨⟨q.c0.a, q.c0.b⟩, ⟨q.c1.a, q.c1.b⟩⟩
def fromNative (q : FIq_Native.field.QM31) : NDE_Reference.Q :=
  ⟨⟨q.c0.a, q.c0.b⟩, ⟨q.c1.a, q.c1.b⟩⟩
def mapResult {α β : Type} (f : α → β) : Result α → Result β
  | .ok x => .ok (f x)
  | .fail e => .fail e
  | .div => .div

theorem copy_lift (v : U32) :
    mapResult toNative (NDE_Reference.lift_ref v) =
    FIq_Native.pool_v1.pair_forest_copy_terminal.lift_m31 v := by
  simp only [NDE_Reference.lift_ref, mapResult, toNative,
    FIq_Native.pool_v1.pair_forest_copy_terminal.lift_m31,
    FIq_Native.field.CM31.from_m31, FIq_Native.field.QM31.from_cm31,
    FIq_Native.field.M31.ZERO, FIq_Native.field.CM31.ZERO, bind_tc_ok]

theorem semantic_lift (v : U32) :
    mapResult toNative (NDE_Reference.lift_ref v) =
    FIq_Native.pool_v1.pair_forest_semantic_terminal.lift_m31 v := by
  exact copy_lift v

theorem extension_limbs (q : FIq_Native.field.QM31) :
    NDE_Reference.extension_limbs_ref (fromNative q) =
    FIq_Native.state_only_poseidon.extension_limbs q := by
  rfl

#print axioms copy_lift
#print axioms semantic_lift
#print axioms extension_limbs
end NDE_LiftBridge
