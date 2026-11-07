import NNG_ConcreteCalls136
set_option autoImplicit false
namespace AspisR1.NNG_SourceCalls136
open Aeneas Aeneas.Std Result NNG_Emitted

/-- Exact raw source dictionaries, with every equality discharged by the
concrete dictionary below. This is not an abstract child-law hypothesis. -/
structure Sources (c : Calls) (env : RSL.Env) : Prop where
  fromFn : (@Calls.c0 c) = @NNG_StdArray.implementation
  mapErr : (@Calls.c1 c) = @NNG_StdMapErr.run
  pointEq : c.c2 = NNG_Equality136.pointEq
  qeq : c.c3 = NNG_Equality136.qeq
  add : c.c4 = NNG_InstallArithmetic.add
  mul : c.c5 = NNG_InstallArithmetic.mul
  mask : c.c6 = NNG_ModelMask.call
  terminal : c.c7 = NNG_ModelTerminal.call
  claims : c.c8 = NNG_LIBClaims.call env
  mark : c.c9 = fun _ _ => .ok ()
  rounds : (@Calls.c10 c) = @NNG_Model134.rounds
  record : c.c11 = NNG_Install.validatedRecord
  payload : c.c12 = NNG_Install.payload
  circle : (@Calls.c13 c) = @NNG_ModelCircle.call
  state : (@Calls.c14 c) = @NNG_Install.state
  decode : c.c15 = NNG_ModelDecode.call

theorem concrete (env : RSL.Env) : Sources (NNG_ConcreteCalls136.calls env) env :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
#print axioms concrete
end AspisR1.NNG_SourceCalls136
