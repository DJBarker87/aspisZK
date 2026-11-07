import NLT_NativeInvocation
set_option autoImplicit false
noncomputable section
namespace NLT_EraseCompatible
open Aeneas Aeneas.Std Result AspisR1 VTop_Stages NJU_CommonObserved NKE_Free
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep NLT_NativeInvocation
def Local (f : NLT_Interpreted.Uninstalled) (H : Bytes → State)
 {X : Type} (d : aspis_core.digest.Digest32 X) (hash : X) (e observed : Event) : Prop :=
 ∃ (recorded : Event) (input : NLT_NativeWindows.Input recorded),
 NLT_NativeWindows.question recorded=NLT_NativeWindows.question e ∧
 NLT_NativeWindows.Compatible f recorded input ∧
 observed=NLT_NativeWindows.window H d hash recorded input
/-- Reuse the SAME actual cut records when interpreting their already-derived
allocator/ABI fields. Every local compatibility clause is proved by the trace
projection, rather than taken as a caller hypothesis in the final root. -/
theorem erase {H : Bytes → State} {X : Type} {d : aspis_core.digest.Digest32 X} {hash : X}
 {A : Type} (f : NLT_Interpreted.Uninstalled) (p : Program Event A) (result : Result A)
 (records : List (Occurrence H d hash)) (invocation : Invocation H d hash p result records)
 (compatible : ∀ r∈records,NLT_NativeWindows.Compatible f r.entered r.input) :
 NLT_Continuation.Invocation (Local f H d hash) p result (records.map actual) := by
 induction invocation with
 | ret value => exact .ret value
 | prim_ok value next result records tail ih => exact .prim_ok value next result _ (ih compatible)
 | prim_fail error next => exact .prim_fail error next
 | prim_div next => exact .prim_div next
 | call_ok codec seed next record same value decoded result records tail ih =>
   apply NLT_Continuation.Invocation.call_ok codec seed next (actual record) _ value decoded result _
   · exact ⟨record.entered,record.input,same,compatible record (List.mem_cons_self),rfl⟩
   · exact ih (fun r member=>compatible r (List.mem_cons_of_mem _ member))
 | call_fail codec seed next record same error decoded =>
   apply NLT_Continuation.Invocation.call_fail codec seed next (actual record) _ error decoded
   exact ⟨record.entered,record.input,same,compatible record (List.mem_singleton_self _),rfl⟩
 | call_div codec seed next record same decoded =>
   apply NLT_Continuation.Invocation.call_div codec seed next (actual record) _ decoded
   exact ⟨record.entered,record.input,same,compatible record (List.mem_singleton_self _),rfl⟩
set_option pp.proofs false
#print erase
#print axioms erase
end NLT_EraseCompatible
