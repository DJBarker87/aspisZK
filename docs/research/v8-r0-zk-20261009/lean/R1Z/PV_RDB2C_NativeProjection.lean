import R1Z.PV_RDB2C_FullResources
import R1Z.PV_RDB2C_WeightsInstance
namespace R1Z.PV_RDB2C_NativeProjection
open Aeneas Aeneas.Std Result PV_RDB2C_PublicRequests
open PV_B2_F_MaterializeNative

def event {S : Type} (decision : Option Nat × S) : Outcome :=
  match decision.1 with | none => .denied | some _ => .supplied

def forget {S : Type} (r : Result (Result PV_RDB2C_V258.RustResult × PV_RDB2C_V258.World S)) :
    Result PV_RDB2C_V258.RustResult := do
  let (value,_) ← r
  value

theorem materialize_projection {S : Type} (allocation : Result (Option Nat × S))
    (w : W) (kappa : Native) (world : PV_RDB2C_V258.World S) :
    PV_B2_E_OrdinaryOriginal.mapResult mapRust
      (forget (PV_RDB2C_PrimitiveResults.materialize (fun _ _ => allocation)
        w (fromNative kappa) world)) =
    callback (PV_B2_E_OrdinaryOriginal.mapResult event allocation) w kappa := by
  cases allocation with
  | fail e => rfl
  | div => rfl
  | ok decision =>
    rcases decision with ⟨p,state⟩
    cases p <;> rfl

open PV_B2_F_ConstructorCarrier

def boxDecision {S : Type} (oom : Error) (allocation : Result (Option Nat × S)) : Result Unit := do
  let (p,_) ← allocation
  match p with | none => fail oom | some _ => ok ()

def eraseBox {S : Type} (oom : Error)
    (r : Result (PV_RDB2C_V259.Returned × PV_RDB2C_V259.World S)) :
    Result PV_B2_F_ConstructorEffect.RustResult := do
  let (value,_) ← r
  match value with
  | .error _ => fail oom
  | .ok (.Err e) => ok (.Err (toError e))
  | .ok (.Ok (_,value)) => ok (.Ok (toWeight value))

theorem constructor_projection {S : Type} (oom : Error) (allocation : Result (Option Nat × S))
    (v : NV) (alpha : Array NQ 10#usize) (z : Array NP 2#usize)
    (world : PV_RDB2C_V259.World S) :
    eraseBox oom (PV_RDB2C_PrimitiveResults.boxed (fun _ _ => allocation)
      (fromVariant v) (amap fromQ alpha) (amap fromPoint z) world) =
      PV_B2_F_ConstructorEffect.copied (boxDecision oom allocation) v alpha z := by
  obtain ⟨value,hvalue⟩ := PV_B2_C_ConstructorSuccess.new_total (fromVariant v)
    (amap fromQ alpha) (amap fromPoint z)
  cases allocation with
  | fail e =>
    simp only [eraseBox,PV_RDB2C_PrimitiveResults.boxed,
      PV_B2_F_ConstructorEffect.copied,hvalue,bind_tc_ok,bind_tc_fail,
      PV_B2_F_ConstructorEffect.finish,boxDecision]
  | div =>
    simp only [eraseBox,PV_RDB2C_PrimitiveResults.boxed,
      PV_B2_F_ConstructorEffect.copied,hvalue,bind_tc_ok,bind_tc_div,
      PV_B2_F_ConstructorEffect.finish,boxDecision]
  | ok decision =>
    rcases decision with ⟨p,state⟩
    cases p <;> simp only [eraseBox,PV_RDB2C_PrimitiveResults.boxed,
      PV_B2_F_ConstructorEffect.copied,hvalue,bind_tc_ok,bind_tc_fail,
      PV_B2_F_ConstructorEffect.finish,boxDecision,PV_RDB2C_V259.finish,
      PV_RDB2C_Box.lowered] <;> rfl

#print axioms materialize_projection
#print axioms constructor_projection
end R1Z.PV_RDB2C_NativeProjection
