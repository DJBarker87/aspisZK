import NDE_Reference2.Funs
import NDE_LiftBridge
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NDE_RawBridge

def toNative (q : NDE_Reference2.Q) : FIq_Native.field.QM31 :=
  ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩

theorem reduce_reference (x : U64) :
    NDE_Reference2.reduce_ref x = FIq_Native.field.M31.reduce_u62 x := by
  unfold NDE_Reference2.reduce_ref FIq_Native.field.M31.reduce_u62 FIq_Native.field.reduce_u64
  simp only [FIq_Native.field.P, bind_tc_ok]

theorem map_bind {α β γ : Type} (f : β → γ) (r : Result α) (k : α → Result β) :
    NDE_LiftBridge.mapResult f (r >>= k) =
    r >>= fun x => NDE_LiftBridge.mapResult f (k x) := by
  cases r <;> rfl

theorem extension_raw (limbs : Array U64 4#usize) :
    NDE_LiftBridge.mapResult toNative (NDE_Reference2.extension_raw_ref limbs) =
    FIq_Native.state_only_poseidon.extension_from_raw_limbs limbs := by
  simp only [NDE_Reference2.extension_raw_ref,
    FIq_Native.state_only_poseidon.extension_from_raw_limbs, map_bind,
    reduce_reference, FIq_Native.field.CM31.new, bind_tc_ok]
  rfl

#print axioms reduce_reference
#print axioms map_bind
#print axioms extension_raw
end NDE_RawBridge
