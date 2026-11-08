import NMX_R8_Code241
import NMX_R8_CodecGroup
import NMX_R8_Emit241
import NMX_R6_SourceExact242
set_option autoImplicit false
noncomputable section
namespace NMX_R8_Children241
open Aeneas Aeneas.Std Result AdapterRw NMS_R2N_Interpreted
abbrev V := LIBB_V2Star.library

def validate (choices : NMX_R4_Authentication.Choices)
 (p : solana_pubkey.Pubkey) (a : Slice r1_pool_adapter.owned.OwnedAccount)
 (d : Slice U8) (s : core.result.Result U64 solana_program_error.ProgramError) :
 RSL.Spec (core.result.Result r1_pool_adapter.ValidatedAsqa solana_program_error.ProgramError) :=
 fun env o => o = NMX_R6_NativeLive242.observation choices p a d s env

def grouped (choices : NMX_R4_Authentication.Choices) : NMX_R8_Code241.Effects RSL.Spec := {
 op11 := fun _ pub proof ck _ _ => NMX_R7_VerifierSource241.meaning pub proof ck
 op22 := NMX_R7_Encoder241.mapped
 op44 := NMS_R2ErrorSource.callback V NMX_R7_Error241.embed
 op53 := NMX_R8_Emit241.meaning
 validate := validate choices
 data := NMS_R2N_GetterMeaning.meaning
}

def original (choices : NMX_R4_Authentication.Choices) : NMS_Effect241.Effects RSL.Spec := {
 op11 := (grouped choices).op11
 op22 := fun s => liftResult (NMX_R8_CodecGroup.code s)
 op44 := (grouped choices).op44
 op53 := (grouped choices).op53
 validate := validate choices
 data := NMS_R2N_GetterMeaning.meaning
}

/-- The source242 call has the exact complete candidate observation at the
original arguments. No new decoder, own-input or successful-return premise. -/
theorem validate_full (choices : NMX_R4_Authentication.Choices)
 (p : solana_pubkey.Pubkey) (a : Slice r1_pool_adapter.owned.OwnedAccount)
 (d : Slice U8) (s : core.result.Result U64 solana_program_error.ProgramError) :
 Simulates (NMS_R2N_RSLError.reply NMX_R5_AfterAuth242.value)
  (validate choices p a d s)
  (NMS_R2Refine.observed (NMX_R6_Validation.validate choices) (NMX_R5_Native242.args p a d s)) := by
 intro env o run
 subst o
 exact (NMX_R6_SourceExact242.observed choices p a d s env).symm

#print axioms validate_full
end NMX_R8_Children241
end
