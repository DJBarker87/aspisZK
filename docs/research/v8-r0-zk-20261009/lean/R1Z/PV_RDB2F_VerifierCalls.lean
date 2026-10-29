import R1Z.PV_RDB2F_SamplerCalls
import R1Z.PV_RDB2F_CapturedQuotient
namespace R1Z.PV_RDB2F_VerifierCalls
open Aeneas Aeneas.Std Result ProverRwFull PV_B2_E_OrdinaryOriginal
set_option autoImplicit false
noncomputable section
/-- Exact scalar call continuation: block has already updated transcript state;
branch on nonzero, then trace::value(4,row,out), then return out. The block and
trace effects are identical on both sides and no dictionary is changed. -/
theorem scalar_consumed_call [ExternalTypes] {World : Type} (ops : ExternalFuns)
    (nonzero : Bool) (block : Bytes) (world : World)
    (trace : Nat → Native → World → Result World) :
    (do let out ← if nonzero then mapResult toNative (PV_RDB2F_Iterator.gamma block)
                  else mapResult toNative (PV_RDB2F_Iterator.ordinary block)
        let world ← trace 4 out world
        ok (out,world))=
    (do let out ← if nonzero then (PV_B2_E_GammaOriginal.selected ops).op249 block
                  else (PV_B2_E_Install250.selected ops).op250 block
        let world ← trace 4 out world
        ok (out,world)) := by
  cases nonzero <;> simp only [Bool.false_eq_true,if_false,if_true,
    PV_RDB2F_SamplerCalls.gamma_callback,PV_RDB2F_SamplerCalls.ordinary_callback]

#print axioms scalar_consumed_call
end
end R1Z.PV_RDB2F_VerifierCalls
