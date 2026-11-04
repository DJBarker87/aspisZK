import PV_STX_EntropyCleanup
import PV_STX_Machine
set_option autoImplicit false
noncomputable section
namespace PV_STX_EntropyEndings
open Aeneas Aeneas.Std ProverRwFull PV_STX_Code PV_STX_Machine
open PV_STX_EntropyCleanup
variable [ExternalTypes] [ExternalFuns]

/-- The actual lifted loop's exhaustion guard. It does not issue a seventeenth
fill or execute a supplied failure continuation. Stack admission at the enclosing
native call is separate and is not inferred from this three-transition suffix. -/
theorem exhausted_suffix {W E : Type} (handler : Handler Request W E)
    (nonce : Array U8 32#usize) (limit retry : Usize) (w : W)
    (stop : ¬retry < limit) :
    run handler 3 (entropyLoop nonce limit retry) w =
      ⟨.returned (.ok (.Err .RepeatedZeroBlock)),w,[]⟩ := by
  simp only [entropyLoop,entropyBody,stop,if_false,Bind.bind,Pure.pure,
    run,advance,start,step,resumed,continueWith,List.nil_append]

/-- This branch is already at the machine's actual source body, not a model
retry or a supplied whole-helper Result. -/
theorem exhausted_body {W E : Type} (handler : Handler Request W E)
    (nonce : Array U8 32#usize) (limit retry : Usize) (w : W)
    (stop : ¬retry < limit) :
    run handler 1 (entropyBody nonce limit retry) w =
      ⟨.returned (.ok (.done (.Err .RepeatedZeroBlock))),w,[]⟩ := by
  simp only [entropyBody,stop,if_false,Pure.pure,
    run,advance,start,step,resumed,continueWith,List.nil_append]

#print axioms exhausted_suffix
#print axioms exhausted_body
end PV_STX_EntropyEndings
