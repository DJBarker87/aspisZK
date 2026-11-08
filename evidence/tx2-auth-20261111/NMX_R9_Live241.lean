import NMX_R9_Native241
set_option autoImplicit false
noncomputable section
namespace NMX_R9_Live241
open Aeneas Aeneas.Std Result AdapterRw NMX_R6_Nonempty

theorem validate (choices : NMX_R4_Authentication.Choices)
 (p : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount)
 (data : Slice U8) (slot : core.result.Result U64 solana_program_error.ProgramError) :
 Live (NMX_R9_Children241.validate choices p accounts data slot) :=
 NMX_R6_NativeLive242.live choices p accounts data slot

theorem encoder (s : LIBB_PoolCarriers.Statement) : Live (NMX_R7_Encoder241.mapped s) := by
 apply NMX_R6_Nonempty.mapped
 exact NMX_R6_Nonempty.lift _

theorem error (e : aspis_r1_cost_probe.verifier.Error) :
 Live (NMS_R2ErrorSource.callback LIBB_V2Star.library NMX_R7_Error241.embed e) :=
 fun env => ⟨_,(NMS_R2ErrorSource.callback_obs _ _ e env _).mpr (Or.inl rfl)⟩

theorem mapped_error (r : core.result.Result Unit aspis_r1_cost_probe.verifier.Error) :
 Live (NMS_Effect241.mapError r (NMS_R2ErrorSource.callback LIBB_V2Star.library NMX_R7_Error241.embed)) := by
 cases r with
 | Ok value => exact NMX_R6_Nonempty.pure _
 | Err e =>
   apply NMX_R6_Nonempty.bind _ _ (error e)
   intro pe
   exact NMX_R6_Nonempty.pure _

attribute [local irreducible] NMX_R9_Children241.validate NMX_R7_Encoder241.mapped
 NMX_R7_VerifierSource241.meaning NMX_R8_Emit241.meaning NMS_R2N_GetterMeaning.meaning
 NMS_R2ErrorSource.callback

theorem grouped (ops : Ops) (choices : NMX_R4_Authentication.Choices)
 (p : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount)
 (data : Slice U8) (slot : core.result.Result U64 solana_program_error.ProgramError) :
 Live (NMX_R8_Code241.body ops (NMX_R9_Children241.grouped choices) p accounts data slot) := by
 unfold NMX_R8_Code241.body NMX_R9_Children241.grouped NMX_R8_Children241.grouped
 dsimp only
 repeat' first
 | exact NMX_R9_Live241.validate _ _ _ _ _
 | exact NMX_R9_Live241.encoder _
 | exact NMX_R9_Live241.error _
 | exact NMX_R9_Live241.mapped_error _
 | exact NMX_R7_VerifierSource241.live _ _ _
 | exact NMX_R8_Emit241.live _
 | exact NMX_R6_Nonempty.getter _
 | exact NMX_R6_Nonempty.pure _
 | exact NMX_R6_Nonempty.lift _
 | apply NMX_R6_Nonempty.bind
 | split
 | intro value

theorem live (choices : NMX_R4_Authentication.Choices)
 (p : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount)
 (data : Slice U8) (slot : core.result.Result U64 solana_program_error.ProgramError) :
 Live (NMX_R9_Native241.meaning choices p accounts data slot) := by
 intro env
 change ∃ o, NMS_Effect241.stage2 (NMX_R8_Std241.ops env) (NMX_R9_Children241.original choices)
  p accounts data slot env o
 rw [NMX_R9_GroupHead241.source]
 exact grouped _ choices p accounts data slot env

/-- A source selection, never an existential choice from the target Ref. -/
def observation (choices : NMX_R4_Authentication.Choices)
 (p : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount)
 (data : Slice U8) (slot : core.result.Result U64 solana_program_error.ProgramError) (env : RSL.Env) :=
 Classical.choose (live choices p accounts data slot env)

theorem source_member (choices : NMX_R4_Authentication.Choices)
 (p : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount)
 (data : Slice U8) (slot : core.result.Result U64 solana_program_error.ProgramError) (env : RSL.Env) :
 NMX_R9_Native241.meaning choices p accounts data slot env (observation choices p accounts data slot env) :=
 Classical.choose_spec (live choices p accounts data slot env)
#print axioms validate
#print axioms encoder
#print axioms error
#print axioms mapped_error
#print axioms grouped
#print axioms live
#print axioms source_member
end NMX_R9_Live241
end
