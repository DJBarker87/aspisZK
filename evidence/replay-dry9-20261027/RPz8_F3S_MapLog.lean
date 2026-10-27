import RPz8_F3R_SdkPure
set_option autoImplicit false
namespace AspisR1.F3S_MapLog
open Aeneas Aeneas.Std Result CheckpointBytes5Effect
 theorem run_map {A B : Type} (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (p : Code A) (f : A → B) (before : SdkC_Source.Log) :
    (SdkC_Source.run hashv (CheckpointBytes5Effect.bind p (fun a=>.done (f a))) before).2=
      (SdkC_Source.run hashv p before).2 := by
  induction p generalizing before with
  | done a => rfl
  | step r k ih => cases r <;> first | rfl | exact ih _ _
  | read parts k ih =>
    cases h : hashv parts <;> simp only [CheckpointBytes5Effect.bind,SdkC_Source.run,h]
    all_goals first | rfl | exact ih _ _
#print axioms run_map
end AspisR1.F3S_MapLog
