import CuSavingsCanonicalFieldStream
import CuSavingsCanonicalDotPartialsCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.CuSavingsRetainedFinishDotClients
open Aeneas Aeneas.Std Result AspisR1CanonicalDots
abbrev E := field.wide_exact.WideExact
abbrev K := field.QM31
abbrev Rows := Array E 4#usize
abbrev High := Array K 4#usize→Result (core.result.Result E verifier.Error)
abbrev SharedOutput := core.result.Result (Rows×High) verifier.Error
structure Clients where
  plain : Slice U8→Slice K→Usize→Result (core.result.Result E verifier.Error)
  shared : Slice U8→Array K 16#usize→Result SharedOutput
  final : Slice U8→Slice K→Result (core.result.Result E verifier.Error)
variable [Shared]
def oldShared (f : Slice U8) (common : Array K 16#usize) : Result SharedOutput := do
  let rows ← old_clients.shared_partials f common
  match rows with
  | .Err e=>.ok (.Err e)
  | .Ok values=>.ok (.Ok (values,old_clients.shared_high values))
def newShared (f : Slice U8) (common : Array K 16#usize) : Result SharedOutput := do
  let rows ← new_clients.shared_partials f common
  match rows with
  | .Err e=>.ok (.Err e)
  | .Ok values=>.ok (.Ok (values,new_clients.shared_high values))
def oldClients : Clients := ⟨old_stream.field_stream,oldShared,old_clients.final_stream⟩
def newClients : Clients := ⟨new_stream.field_stream,newShared,new_clients.final_stream⟩

theorem shared_equivalence (f : Slice U8) (common : Array K 16#usize) :
    newShared f common=oldShared f common :=
  CuSavingsCanonicalDotPartialsCanonical.caller_context f common
    (fun e=>.ok (.Err e)) (fun values high=>.ok (.Ok (values,high)))

/-- The fixed source client dictionary is globally equal. No factor/scalar
canonicality is assumed: only E-wide checks changed; raw K checks remain. -/
theorem clients_equivalence : newClients=oldClients := by
  have plain : new_stream.field_stream=old_stream.field_stream := by
    funext f scratch n
    exact CuSavingsCanonicalFieldStream.source_equivalence f scratch n
  have shared : newShared=oldShared := by
    funext f common
    exact shared_equivalence f common
  have final : new_clients.final_stream=old_clients.final_stream := by
    funext f weights
    exact CuSavingsCanonicalDotClients.final_equivalence f weights
  change Clients.mk _ _ _=Clients.mk _ _ _
  rw [plain,shared,final]

#print axioms shared_equivalence
#print axioms clients_equivalence
end AspisR1.CuSavingsRetainedFinishDotClients
