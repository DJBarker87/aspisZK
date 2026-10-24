import Lean
import S6SdkDependencyFactorV1
set_option autoImplicit false
open Lean Elab Term
namespace AspisS6SdkFirstObjectEquivalence
def readComplete (p : System.FilePath) : IO ModuleData := do
  let mut files := #[p]
  for suffix in [".server", ".private"] do
    let q : System.FilePath := p.toString ++ suffix
    if ← q.pathExists then files := files.push q
  let parts ← readModuleDataParts files
  let some (data, _) := parts.toList.getLast? | throw (IO.userError "empty module")
  pure data

/-- Supply the exact old cached body as an UNTRUSTED term. The ordinary Lean
kernel checks originalFirst and the equality below. No environment insertion,
axiom, unsafe input or unchecked declaration construction is used. -/
elab "s6_original_first_body" : term => do
  let data ← readComplete "/tmp/s126-s6-sdk-first-20261024-cache/recovered/S2W_D189Wrappers.olean"
  let some c := data.constants.find? (fun c => c.name == `AspisR1.S2W_D189Wrappers.first)
    | throwError "missing pinned original wrapper"
  let some value := c.value? | throwError "original wrapper has no body"
  return value

def originalFirst := s6_original_first_body

/-- Definitional equality of the original cached complete first-wrapper body
and the factored complete source wrapper, despite generated-match differences. -/
theorem first_eq_original : @AspisR1.S2W_D189Wrappers.first = @originalFirst := by
  rfl

#print axioms originalFirst
#print axioms first_eq_original
end AspisS6SdkFirstObjectEquivalence
