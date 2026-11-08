import NMX_R4_ObservedStep
set_option autoImplicit false
noncomputable section
namespace NMX_R4_PdaObservation
open Aeneas Aeneas.Std Result AdapterRw NMX_OwnedPackets NMX_R4_CallProgram NMX_R4_CallRun

def after (f : core.ops.function.FnOnce Unit solana_pubkey.PubkeyError PE)
 (r : core.result.Result solana_pubkey.Pubkey solana_pubkey.PubkeyError)
 (k : solana_pubkey.Pubkey → Program (core.result.Result Auth PE)) : Program (core.result.Result Auth PE) := do
 let mapped ← scalar (core.result.Result.map_err f r ())
 NMX_R4_TryObservation.after mapped k

theorem mapped_error (c : Context)
 (f : core.ops.function.FnOnce Unit solana_pubkey.PubkeyError PE)
 (errorLaw : f.call_once () .InvalidSeeds = .ok .InvalidAccountData)
 (k : solana_pubkey.Pubkey → Program (core.result.Result Auth PE)) :
 observe c (after f (.Err .InvalidSeeds) k) = ⟨.ret (.error .invalidAccountData),[]⟩ := by
 change observe c (NMX_R4_CallProgram.bind
  (scalar (core.result.Result.map_err f (.Err .InvalidSeeds) ()))
  (fun mapped => NMX_R4_TryObservation.after mapped k)) = _
 rw [NMX_R4_CallLaws.observed_scalar]
 have mapped : core.result.Result.map_err f (.Err .InvalidSeeds) () =
     .ok (.Err .InvalidAccountData : core.result.Result solana_pubkey.Pubkey PE) := by
   change (do let copied ← f.call_once () .InvalidSeeds; Result.ok (core.result.Result.Err copied : core.result.Result solana_pubkey.Pubkey PE)) = _
   rw [errorLaw]
   rfl
 rw [mapped]
 rfl

theorem mapped_ok (c : Context)
 (f : core.ops.function.FnOnce Unit solana_pubkey.PubkeyError PE)
 (key : solana_pubkey.Pubkey)
 (k : solana_pubkey.Pubkey → Program (core.result.Result Auth PE)) :
 observe c (after f (.Ok key) k) = observe c (k key) := by
 change observe c (NMX_R4_CallProgram.bind
  (scalar (core.result.Result.map_err f (.Ok key) ()))
  (fun mapped => NMX_R4_TryObservation.after mapped k)) = _
 rw [NMX_R4_CallLaws.observed_scalar]
 simp only [core.result.Result.map_err,AspisR1.Port4C_GeometryStd.mapError,
  NMX_R3_RegistryRun.scalar,NMX_R2_Observation.bind,NMX_R4_TryObservation.success,List.nil_append]

theorem step (c : Context) (seeds : Slice (Slice U8)) (program : solana_pubkey.Pubkey)
 (f : core.ops.function.FnOnce Unit solana_pubkey.PubkeyError PE)
 (errorLaw : f.call_once () .InvalidSeeds = .ok .InvalidAccountData)
 (k : solana_pubkey.Pubkey → Program (core.result.Result Auth PE))
 (next : solana_pubkey.Pubkey → NMX_Program.Program Auth)
 (tail : ∀ a, observe c (k a) =
 NMX_R2_NativeExecution.run c.owners c.allocations c.failure c.lane c.registry c.env (next a)) :
 observe c (NMX_R4_CallProgram.bind (pda seeds program) (fun r => after f r k)) =
 NMX_R2_NativeExecution.run c.owners c.allocations c.failure c.lane c.registry c.env
 (NMX_Program.bind (NMX_SourceProgram.call (.pda seeds program)) next) := by
 rw [NMX_R4_CallLaws.observed_bind]
 unfold pda
 rw [NMX_R4_CallLaws.run_call]
 cases reply : c.env.pda (seeds.val.map NMX_R2_Carrier.bytes) (NMX_R2_Carrier.key program) with
 | none =>
   simp only [command,reply,NMX_R2_Observation.bind,mapped_error c f errorLaw,
    NMX_Program.bind,NMX_SourceProgram.call,NMX_R2_NativeExecution.run,
    NMX_R2_NativeExecution.command,NMX_R2_Observation.rustBind,NMX_R2_Observation.bind,List.append_nil]
 | some key =>
   simp only [command,reply,NMX_R2_Observation.bind,mapped_ok,
    NMX_Program.bind,NMX_SourceProgram.call,NMX_R2_NativeExecution.run,
    NMX_R2_NativeExecution.command,NMX_R2_Observation.rustBind,NMX_R2_Observation.bind,tail]

#print axioms mapped_error
#print axioms mapped_ok

#print axioms step
end NMX_R4_PdaObservation
end
