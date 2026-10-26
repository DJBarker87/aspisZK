import F3R_SdkPure
set_option autoImplicit false
namespace AspisR1.F3S_Silent
open Aeneas Aeneas.Std Result CheckpointBytes5Effect
 theorem lift_log {A : Type} (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (r : Result A) :
    SdkC_Source.readLog (SdkC_Source.run hashv (liftResult r) []).2=[] := by
  cases r <;> rfl
#print axioms lift_log
end AspisR1.F3S_Silent
