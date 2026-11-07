import NMX_ErrorCloneCut
import NMX_ResultRelation
import NMX_Heterogeneous
set_option autoImplicit false
namespace NMX_NecessaryConditions
open Aeneas Aeneas.Std AdapterRw NMX_Carrier
/-- Any full observation transport for this getter must exclude a stopped
error clone. This is conditional on the actual reached std result; it does
not supply a runtime failure witness or a new row input clause. -/
theorem getter_stop_excluded (ops : Ops) (a : r1_pool_adapter.owned.OwnedAccount)
 (e : solana_program_error.ProgramError) (deferred : a.bytes = .Err e)
 (failure : Aeneas.Std.Error) (env : RSL.Env)
 (transport : NMX_Heterogeneous.Refines bytes
   (NMX_ResultRelation.rust (r1_pool_adapter.owned.OwnedAccount.data ops a))
   (RSL.RS.ofExcept (RSL.OwnedAccount.data (account a)))) :
 ops.op35 e ≠ .fail failure := by
 intro stops
 have native := NMX_ErrorCloneCut.data_stop ops a e deferred failure stops
 have law := transport env ⟨.abort,[]⟩ (by
  change ⟨.abort,[]⟩ = NMX_ObserveResult.observe id _
  rw [native]
  rfl)
 change RSL.RS.ofExcept (reply (fun b => b.val.map byte) a.bytes) _ ⟨.abort,[]⟩ at law
 rw [deferred] at law
 change (⟨.abort,[]⟩ : RSL.Obs (Except RSL.ProgramError RSL.Bytes)) =
  ⟨.ret (.error (error e)),[]⟩ at law
 have impossible := congrArg RSL.Obs.exit law
 cases impossible
#print axioms getter_stop_excluded
end NMX_NecessaryConditions
