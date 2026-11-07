import NMS_R2ErrorMeaning
import NMS_R2N_Interpreted
import NMS_R2N_RSLError
import NMS_Effect241
set_option autoImplicit false
noncomputable section
namespace NMS_R2ErrorSource
open Aeneas Aeneas.Std AdapterRw
open RSL RSL.TX2_241
abbrev NativeError := aspis_r1_cost_probe.verifier.Error
/-- Independent source-site interpretation: format! allocation precedes
sol_log, and lib.rs::error then returns the full native ProgramError. -/
def callback (V : V2Lib) (embed : NativeError → V.VErr) (e : NativeError) :
 Spec solana_program_error.ProgramError :=
 Spec.bind Spec.alloc fun _ =>
 Spec.bind (Spec.emit (.log ("r1:error:" ++ V.debug (embed e)))) fun _ =>
 Spec.pure .InvalidInstructionData

theorem callback_obs (V : V2Lib) (embed : NativeError → V.VErr) (e : NativeError)
 (env : Env) (o : Obs solana_program_error.ProgramError) :
 callback V embed e env o ↔
 o = ⟨.ret .InvalidInstructionData,[.log ("r1:error:" ++ V.debug (embed e))]⟩ ∨
 o = ⟨.abort,[]⟩ := by
 unfold callback
 rw [Spec.bind_two _ _ env () (fun _ => Iff.rfl)]
 simp [Spec.bind,Spec.emit,Spec.pure]

def verifierReply (V : V2Lib) (embed : NativeError → V.VErr) :
 core.result.Result Unit NativeError → Except V.VErr Unit
 | .Ok () => .ok ()
 | .Err e => .error (embed e)

theorem source_obs (V : V2Lib) (embed : NativeError → V.VErr) (e : NativeError)
 (env : Env) (o : Obs (core.result.Result Unit solana_program_error.ProgramError)) :
 NMS_Effect241.mapError (.Err e) (callback V embed) env o ↔
 o = ⟨.ret (.Err .InvalidInstructionData),[.log ("r1:error:" ++ V.debug (embed e))]⟩ ∨
 o = ⟨.abort,[]⟩ := by
 change Spec.bind (callback V embed e)
   (fun pe => Spec.pure (core.result.Result.Err pe : core.result.Result Unit solana_program_error.ProgramError)) env o ↔ _
 simp [Spec.bind,callback_obs,Spec.pure]

theorem target_obs (V : V2Lib) (e : V.VErr) (env : Env)
 (o : Obs (Except ProgramError Unit)) :
 mapVErr V (.error e) env o ↔
 o = ⟨.ret (.error .invalidInstructionData),[.log ("r1:error:" ++ V.debug e)]⟩ ∨
 o = ⟨.abort,[]⟩ := by
 change RS.seq (RS.lift Spec.alloc)
  (RS.seq (RS.lift (Spec.emit (.log ("r1:error:" ++ V.debug e))))
   (RS.throw .invalidInstructionData)) env o ↔ _
 rw [RS.alloc_seq_iff]
 simp [RS.seq,RS.bind,RS.lift,Spec.map,Spec.bind,Spec.emit,Spec.pure,RS.throw]

/-- Complete emitted callback composition: both returned branches and the
new format-allocation abort. The error carrier map keeps every payload. -/
theorem full (V : V2Lib) (embed : NativeError → V.VErr)
 (r : core.result.Result Unit NativeError) :
 NMS_R2N_Interpreted.Simulates (NMS_R2N_RSLError.reply id)
  (NMS_Effect241.mapError r (callback V embed)) (mapVErr V (verifierReply V embed r)) := by
 cases r with
 | Ok unit => cases unit; exact NMS_R2N_Interpreted.pure _ _
 | Err e =>
   intro env o run
   rcases (source_obs V embed e env o).mp run with same | same
   · subst o
     exact (target_obs V (embed e) env _).mpr (Or.inl rfl)
   · subst o
     exact (target_obs V (embed e) env _).mpr (Or.inr rfl)
#print axioms callback_obs
#print axioms source_obs
#print axioms target_obs
#print axioms full
end NMS_R2ErrorSource
