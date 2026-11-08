import NMX_R6_NativeLeft242
import NMX_R6_Validation
set_option autoImplicit false
noncomputable section
namespace NMX_R6_SourceExact242
open Aeneas Aeneas.Std Result AdapterRw NMS_R2N_Interpreted

/-- Observed source association at the EXACT original native tuple. Reification
is identity, not a different representative with only equal lengths. -/
theorem observed (choices : NMX_R4_Authentication.Choices)
 (p : solana_pubkey.Pubkey) (as_ : Slice r1_pool_adapter.owned.OwnedAccount)
 (d : Slice U8) (s : core.result.Result U64 solana_program_error.ProgramError) (env : RSL.Env) :
 NMX_R6_Validation.validate choices (NMX_R5_Native242.args p as_ d s) env =
 mapObs (NMS_R2N_RSLError.reply NMX_R5_AfterAuth242.value)
  (NMX_R6_NativeLive242.observation choices p as_ d s env) := by
 rw [NMX_R6_Validation.native_branch]
 simp only [NMX_R6_NativeLeft242.program,NMX_R6_NativeLeft242.accounts,
  NMX_R6_NativeLeft242.data,NMX_R6_NativeLeft242.slot]

/-- A concrete observation of the complete emitted source meaning at the same
arguments produces the candidate observation, including errors/stops/events. -/
theorem source (choices : NMX_R4_Authentication.Choices)
 (p : solana_pubkey.Pubkey) (as_ : Slice r1_pool_adapter.owned.OwnedAccount)
 (d : Slice U8) (s : core.result.Result U64 solana_program_error.ProgramError) (env : RSL.Env) :
 ∃ o, NMS_R2N_Native242Children.meaning false (NMX_R4_NMS233.typed choices) p as_ d s env o ∧
 NMX_R6_Validation.validate choices (NMX_R5_Native242.args p as_ d s) env =
  mapObs (NMS_R2N_RSLError.reply NMX_R5_AfterAuth242.value) o :=
 ⟨_,NMX_R6_NativeLive242.source_member choices p as_ d s env,observed choices p as_ d s env⟩
#print axioms observed
#print axioms source
end NMX_R6_SourceExact242
end
