import NMX_PdaCarrier
import NMX_AllocationSound
set_option autoImplicit false
namespace NMX_PdaSound
open RSL NMX_Observation
/-- Exact syscall reply/error and singleton event are admitted by the
canonical PDA command at the SAME ordered byte seeds and program key. -/
theorem observation (seeds : List Bytes) (program : B32) (env : Env) :
 pdaOrErr seeds program env
 ⟨.ret (match env.pda seeds program with
   | none => .error .invalidAccountData
   | some key => .ok key),[.pda seeds program (env.pda seeds program)]⟩ := by
 have first := NMX_AllocationSound.lift
   ⟨.ret (env.pda seeds program),[.pda seeds program (env.pda seeds program)]⟩
   (pdaCall seeds program) env (NMX_PdaCarrier.call seeds program env)
 have head : RS.lift (pdaCall seeds program) env
  ⟨.ret (.ok (env.pda seeds program)),[.pda seeds program (env.pda seeds program)]⟩ := by
  simpa only [NMX_Observation.bind,List.append_nil] using first
 have complete := rust_sound
  ⟨.ret (.ok (env.pda seeds program)),[.pda seeds program (env.pda seeds program)]⟩
  (fun r : Option B32 => ⟨.ret (match r with | none => .error .invalidAccountData | some k => .ok k),[]⟩)
  (RS.lift (pdaCall seeds program)) (fun r => RS.ofOption r .invalidAccountData) env head
  (by intro r;cases r <;> rfl)
 simpa only [pdaOrErr,NMX_Observation.rustBind,NMX_Observation.bind,List.append_nil] using complete
#print axioms observation
end NMX_PdaSound
