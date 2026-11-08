import NNG_Tree328
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Tail328
open Aeneas Aeneas.Std Result NMT_CallTree NNG_Observed136 NNG_Carriers328

theorem source (env : RSL.Env) (r : core.result.Result (alloc.vec.Vec U8) NNG_Carriers328.Error) :
 RSL.TX1_328.mapVErr LIB_Instances.VL (childPort r) env
  (observation port (NNG_Tree328.events env) (NNG_Tree328.tail r)) := by
 cases r with
 | Ok bytes=>rfl
 | Err e=>
  have same : observation port (NNG_Tree328.events env) (NNG_Tree328.tail (.Err e))=
   ⟨.ret (.error .invalidInstructionData),NNG_Error328.events e⟩ := by
   change (⟨.ret (.error .invalidInstructionData),
    NNG_Tree328.events env (.call "lib.rs::error" e (ok NMT_first.solana_program_error.ProgramError.InvalidInstructionData))++[]⟩ :
     RSL.Obs (Except RSL.ProgramError RSL.Bytes))=_
   rw [NNG_Tree328.error_call,List.append_nil]
  exact Eq.mp (congrArg (RSL.TX1_328.mapVErr LIB_Instances.VL (childPort (.Err e)) env) same.symm)
   (NNG_Error328.target e env)
#print axioms source
end AspisR1.NNG_Tail328
