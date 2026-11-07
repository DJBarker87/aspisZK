import NMS_R2N_Interpreted
import NMS_R2N_RSLScalars
import NNC_ByteCarriers
import NND_Returned
import RSL_Verifier
set_option autoImplicit false
namespace LIB_Carriers
open Aeneas Aeneas.Std
abbrev bytes := NMS_R2N_RSLScalars.bytes
abbrev b32 := NMS_R2N_RSLScalars.b32
abbrev rawBytes := NNC_ByteCarriers.nativeList
/-- The graph of a deterministic value and its exact ordered effects. -/
def graph {A : Type} (value : RSL.Env → A)
    (events : RSL.Env → List RSL.Event) : RSL.Spec A :=
  fun env o => o = ⟨.ret (value env), events env⟩
/-- Preserve the native stop distinction; stops retain exactly this prefix. -/
def resultObs {A B : Type} (value : A → B) (events : List RSL.Event) :
    Result A → RSL.Obs B
  | .ok x => ⟨.ret (value x), events⟩
  | .fail _ => ⟨.abort, events⟩
  | .div => ⟨.diverge, events⟩
def resultGraph {A B : Type} (value : A → B)
    (model : RSL.Env → Result A) (events : RSL.Env → List RSL.Event) : RSL.Spec B :=
  fun env o => o = resultObs value (events env) (model env)
def ofFn {A B : Type} (dom : A → Prop) (value : A → RSL.Env → B)
    (events : A → RSL.Env → List RSL.Event) : RSL.Child A B :=
  ⟨dom, fun a => graph (value a) (events a)⟩
theorem graph_returns {A : Type} (value : RSL.Env → A)
    (events : RSL.Env → List RSL.Event) (env : RSL.Env) :
    NND_Returned.Returns (graph value events) env (value env) := by
  intro o r h hr
  subst o
  exact (RSL.Exit.ret.inj hr).symm
theorem ofFn_law {A B : Type} (dom : A → Prop) (value : A → RSL.Env → B)
    (events : A → RSL.Env → List RSL.Event) (a : A) :
    (ofFn dom value events).law a = graph (value a) (events a) := rfl
theorem ofFn_returns {A B : Type} (dom : A → Prop) (value : A → RSL.Env → B)
    (events : A → RSL.Env → List RSL.Event) (a : A) (env : RSL.Env) :
    NND_Returned.Returns ((ofFn dom value events).law a) env (value a env) :=
  graph_returns (value a) (events a) env
theorem bytes_exact (s : Slice U8) : bytes s = NNC_ByteCarriers.host s.val := rfl
theorem bytes_roundtrip (s : Slice U8) : rawBytes (bytes s) = s.val :=
  NNC_ByteCarriers.native_host s.val
theorem byte_roundtrip (s : RSL.Bytes) :
    NNC_ByteCarriers.host (rawBytes s) = s := NNC_ByteCarriers.host_native s
theorem b32_exact (s : Aeneas.Std.Array U8 32#usize) :
    (b32 s).bytes = NNC_ByteCarriers.host s.val := rfl
theorem b32_injective {x y : Aeneas.Std.Array U8 32#usize} (h : b32 x = b32 y) : x = y :=
  NMS_R2N_RSLScalars.b32_injective h
theorem result_ok {A B : Type} (value : A → B) (events : List RSL.Event) (a : A) :
    resultObs value events (.ok a) = ⟨.ret (value a), events⟩ := rfl
theorem result_fail {A B : Type} (value : A → B) (events : List RSL.Event) (e : Error) :
    resultObs value events (.fail e) = ⟨.abort, events⟩ := rfl
theorem result_div {A B : Type} (value : A → B) (events : List RSL.Event) :
    resultObs value events .div = ⟨.diverge, events⟩ := rfl
#print axioms graph_returns
#print axioms ofFn_law
#print axioms ofFn_returns
#print axioms bytes_exact
#print axioms bytes_roundtrip
#print axioms byte_roundtrip
#print axioms b32_exact
#print axioms b32_injective
#print axioms result_ok
#print axioms result_fail
#print axioms result_div
end LIB_Carriers
