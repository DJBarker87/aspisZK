import NNH_MProgramControl
import NNH_MV1DecoderValues
import NND_PoolReturned
set_option autoImplicit false
namespace NNH_MFormatControl
open Aeneas Aeneas.Std Result AdapterRw NND_Carrier NND_Returned NNH_ModelCarrier

def thenCall {A B E : Type} (r : Result (core.result.Result A E))
 (k : A → NNH_MProgramControl.P B) : NNH_MProgramControl.P B := do
 let out ← r
 match out with | .Ok a => k a | .Err _ => ok (.Err .InvalidAccountData)

/-- The exact map_err+? protocol used by registry format children. A concrete
call-site callback discharges hc by rfl; no native child endpoint is assumed. -/
theorem source {A B E O : Type} (r : Result (core.result.Result A E))
 (inst : core.ops.function.FnOnce O E solana_program_error.ProgramError) (op : O)
 (hc : ∀ e, inst.call_once op e = ok .InvalidAccountData)
 (k : A → NNH_MProgramControl.P B) :
 (do let out ← r
     let mapped ← AdapterRw.core.result.Result.map_err inst out op
     let cf ← core.result.Result.Insts.CoreOpsTry.branch mapped
     match cf with
     | core.ops.control_flow.ControlFlow.Continue a => k a
     | core.ops.control_flow.ControlFlow.Break e =>
       core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        B (core.convert.FromSame solana_program_error.ProgramError) e) = thenCall r k := by
 cases r with
 | fail e => rfl
 | div => rfl
 | ok out =>
   cases out with
   | Ok a => rfl
   | Err e =>
     simp only [AdapterRw.core.result.Result.map_err,hc,bind_tc_ok]
     rfl

theorem transport {A B E X Y : Type} (r : core.result.Result A E)
 (k : A → NNH_MProgramControl.P B) (f : A → X) (g : B → Y)
 (F : X → Except RSL.ProgramError Y)
 (hk : ∀ a, outer (reply g) (k a) = ok (F (f a))) :
 outer (reply g) (thenCall (ok r) k) =
 ok (ebind (option (NNH_MV1DecoderValues.asOption f r) .invalidAccountData) F) := by
 cases r with
 | Err e => rfl
 | Ok a => exact hk a

#print axioms source
#print axioms transport
end NNH_MFormatControl
