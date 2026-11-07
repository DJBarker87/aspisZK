import NNG_Native328
import LIB_ErrorDebug
import RSL_TX1_328
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Error328
open RSL Aeneas Aeneas.Std Result NNG_Carriers328

def message (e : NNG_Carriers328.Error) : String := "r1:error:" ++ LIB_Instances.VL.debugV (error e)
def events (e : NNG_Carriers328.Error) : List Event := [.log (message e)]

/-- The CLOSED lib.rs error formatter/syslog bridge, at the SAME error value
and exact literal payload. Its allocation site is handled by target below. -/
theorem source (e : NNG_Carriers328.Error) (log : List Event) :
 NIJ_ErrorJoin.run (fun text history=>ok (history++[.log text]))
  (LIB_ErrorDebug.adapter (error e)) log=
 ok (AdapterRw.solana_program_error.ProgramError.InvalidInstructionData,log++events e) :=
 LIB_ErrorDebug.native_source _ _ _
#print axioms source

theorem target_iff (e : NNG_Carriers328.Error) (env : Env) (o : Obs (Except ProgramError Bytes)) :
 TX1_328.mapVErr LIB_Instances.VL (.error (error e)) env o ↔
 o=⟨.ret (.error .invalidInstructionData),events e⟩ ∨ o=⟨.abort,[]⟩ := by
 unfold TX1_328.mapVErr
 rw [RS.alloc_seq_iff]
 simp [RS.seq,RS.bind,RS.lift,Spec.map,Spec.bind,Spec.emit,Spec.pure,RS.throw,events,message]
#print axioms target_iff

theorem target (e : NNG_Carriers328.Error) (env : Env) :
 TX1_328.mapVErr LIB_Instances.VL (.error (error e)) env
  ⟨.ret (.error .invalidInstructionData),events e⟩ :=
 (target_iff e env _).mpr (Or.inl rfl)
#print axioms target
end AspisR1.NNG_Error328
