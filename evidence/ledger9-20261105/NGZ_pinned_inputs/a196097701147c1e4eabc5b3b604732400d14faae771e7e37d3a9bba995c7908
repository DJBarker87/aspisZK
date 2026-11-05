import Lean
import AspisR1AdapterReconstruct.Funs

-- BEGIN copied NEE_M31SerializerDomain: evidence/slice-s-compose2-20261029/NEE_M31SerializerDomain.lean
set_option autoImplicit false
namespace NFY_NEE_M31SerializerDomain
open Aeneas Aeneas.Std Result AspisR1AdapterReconstruct

/-- The emitted scalar serializer calls the primitive u32 serializer on the
same raw word, including noncanonical representatives. -/
theorem primitive (word : U32) :
    aspis_core.field.M31.to_le_bytes word = ok (core.num.U32.to_le_bytes word) := by rfl

/-- Fixed-array carrier size distinguishes this source call from WideExact's
32-byte serializer. The native source receiver is self.0 : u32. -/
theorem width (word : U32) : (core.num.U32.to_le_bytes word).val.length = 4 := by
  exact (core.num.U32.to_le_bytes word).property

theorem widths_distinct : (4 : Nat) ≠ 32 := by decide

#print axioms primitive
#print axioms width
#print axioms widths_distinct
end NFY_NEE_M31SerializerDomain
-- END copied NEE_M31SerializerDomain

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
