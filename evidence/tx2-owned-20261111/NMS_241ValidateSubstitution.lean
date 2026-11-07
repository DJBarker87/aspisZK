import NMS_Effect241
import NMS_Interpreted
set_option autoImplicit false
noncomputable section
namespace NMS_241ValidateSubstitution
open Aeneas Aeneas.Std AdapterRw NMS_RSLRefine
abbrev Effects := NMS_Effect241.Effects RSL.Spec
/-- Substitution of the complete242 law at the SAME original241 arguments.
Every remaining241 step stays literal, including the actual064 call and its
error callback. This is an intermediate emitted-source fold, not a native root. -/
theorem fold (ops : Ops) (effects : Effects)
 (validate : solana_pubkey.Pubkey → Slice r1_pool_adapter.owned.OwnedAccount → Slice U8 →
   core.result.Result U64 solana_program_error.ProgramError → RSL.Spec
    (core.result.Result r1_pool_adapter.ValidatedAsqa solana_program_error.ProgramError))
 (program : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount)
 (data : Slice U8) (slot : core.result.Result U64 solana_program_error.ProgramError)
 (child : Refines (effects.validate program accounts data slot) (validate program accounts data slot)) :
 Refines (NMS_Effect241.stage2 ops effects program accounts data slot)
  (NMS_Effect241.stage2 ops {effects with validate := validate} program accounts data slot) := by
 unfold NMS_Effect241.stage2
 cases count : (Slice.len accounts != 7#usize) with
 | true => exact refl _
 | false =>
   apply NMS_RSLRefine.bind (refl _)
   intro prefix
   apply NMS_RSLRefine.bind (refl _)
   intro magic
   apply NMS_RSLRefine.bind (refl _)
   intro magicSlice
   apply NMS_RSLRefine.bind (refl _)
   intro different
   cases different with
   | true => exact refl _
   | false =>
     apply NMS_RSLRefine.bind child
     intro reply
     exact refl _
#print axioms fold
end NMS_241ValidateSubstitution
