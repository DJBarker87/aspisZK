import Lean
import ToBytesP6OutputInvariantV1

-- BEGIN copied LPi_EWriter: lean/LPi_EWriter.lean
set_option autoImplicit false
namespace AspisR1.NFY_LPi_EWriter
open Aeneas Aeneas.Std Result
/-- Reuse the unchanged emitted serializer with its explicit P6 iterator model.
Native std/iterator ABI association stays in D188, not in this theorem. -/
theorem source (x : AspisR1WideToBytesSource.field.wide_exact.WideExact) :
    ∃ out, AspisR1WideToBytesSource.field.wide_exact.WideExact.to_le_bytes x = ok out ∧
      out.val = P6ToBytes.OutputInvariant.serializedWords x :=
  P6ToBytes.OutputInvariant.to_le_bytes_output_contents x

#print axioms source
end AspisR1.NFY_LPi_EWriter
-- END copied LPi_EWriter

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
