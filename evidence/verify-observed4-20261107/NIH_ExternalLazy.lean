import NIH_ConstructorReferences
import NDO_JGj_ExternalTotal
import RPv_FJb_ExternalExact
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.NIH_ExternalLazy
open FIv_NativeArithmetic (NQ)
/-- Original nested matrix/column/tail loops, complete Result and same adopted layer. -/
theorem result (s : Array NQ 16#usize) (canonical : FIw_ArrayValue.canonical s) :
 ∃ out, FIq_Native.state_only_poseidon.external_linear_lazy s=ok out ∧
 FIw_ArrayValue.canonical out ∧
 FIw_ArrayValue.decoded out=R0P.poseidonExternalLinear (FIw_ArrayValue.decoded s) := by
 obtain ⟨out,run,_⟩:=JGj_ExternalTotal.source s canonical
 exact ⟨out,run,FJb_ExternalExact.value s out canonical run⟩
#print axioms result
end AspisR1.NIH_ExternalLazy
end
