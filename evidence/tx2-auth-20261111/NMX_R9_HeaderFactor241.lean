import NMX_R9_Children241
import NMX_R8_Factor241
import NMX_R8_Std241
import NMX_R8_MagicCheck
import NMX_R8_ScalarContext
set_option autoImplicit false
noncomputable section
namespace NMX_R9_HeaderFactor241
open Aeneas Aeneas.Std Result AdapterRw NMS_R2N_Interpreted
abbrev Reply := core.result.Result Unit solana_program_error.ProgramError
abbrev magic := aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_MAGIC

def cmp (env : RSL.Env) (first : Option (Slice U8)) :=
 core.cmp.PartialEq.ne.trait_default
  (core.option.Option.Insts.CoreCmpPartialEqOption (NMX_R7_Std241.ops env)
   (core.cmp.PartialEqShared (Slice.Insts.CoreCmpPartialEqSlice core.cmp.PartialEqU8))) first (some magic.to_slice)

theorem magic_scalar (env : RSL.Env) (data : Slice U8) :
 NMX_R7_Prefix241.magicCheck env data =
 (do let first ← core.slice.Slice.get (core.slice.index.SliceIndexRangeToUsizeSlice U8) data ⟨4#usize⟩
     cmp env first) := rfl

def later (env : RSL.Env) (choices : NMX_R4_Authentication.Choices)
 (p : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount)
 (data : Slice U8) (slot : core.result.Result U64 solana_program_error.ProgramError) (bad : Bool) : RSL.Spec Reply :=
 if bad then RSL.Spec.pure (.Err .InvalidInstructionData) else
 NMS_R2N_RawTry.literal (NMX_R9_Children241.validate choices p accounts data slot)
  (fun v => NMX_R8_Factor241.afterValidate (NMX_R8_Std241.ops env) (NMX_R9_Children241.grouped choices) v accounts)

def source (env : RSL.Env) (choices : NMX_R4_Authentication.Choices)
 (p : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount)
 (data : Slice U8) (slot : core.result.Result U64 solana_program_error.ProgramError) : RSL.Spec Reply :=
 if Slice.len accounts != 7#usize then RSL.Spec.pure (.Err .InvalidInstructionData) else
 RSL.Spec.bind (liftResult (NMX_R7_Prefix241.magicCheck env data)) (later env choices p accounts data slot)

theorem factor (env : RSL.Env) (choices : NMX_R4_Authentication.Choices)
 (p : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount)
 (data : Slice U8) (slot : core.result.Result U64 solana_program_error.ProgramError) :
 NMX_R8_Factor241.head (NMX_R8_Std241.ops env) (NMX_R9_Children241.grouped choices) p accounts data slot =
 source env choices p accounts data slot := by
 unfold NMX_R8_Factor241.head source
 dsimp only
 cases count : (Slice.len accounts != 7#usize) with
 | true => rfl
 | false =>
   rw [magic_scalar]
   have grouping := NMX_R8_ScalarContext.context
    (core.slice.Slice.get (core.slice.index.SliceIndexRangeToUsizeSlice U8) data ⟨4#usize⟩)
    (cmp env) (later env choices p accounts data slot)
   rw [←grouping]
   apply congrArg (RSL.Spec.bind _)
   funext first
   change RSL.Spec.bind (RSL.Spec.pure magic) _ = _
   rw [RSL.Spec.bind_pure]
   change RSL.Spec.bind (RSL.Spec.pure magic.to_slice) _ = _
   rw [RSL.Spec.bind_pure]
   apply congrArg (RSL.Spec.bind _)
   funext bad
   unfold later
   cases bad with
   | true => rfl
   | false =>
     unfold NMS_R2N_RawTry.literal
     apply congrArg (RSL.Spec.bind _)
     funext reply
     apply congrArg (RSL.Spec.bind _)
     funext flow
     cases flow <;> rfl
#print axioms magic_scalar
#print axioms factor
end NMX_R9_HeaderFactor241
end
