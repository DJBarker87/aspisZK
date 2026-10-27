import F3N_SourceEffect
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3S_EffectDictionary
open Aeneas Aeneas.Std Result AspisR1Stage2 CheckpointBytes5Effect
 theorem run {A Hash : Type} (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (law : ∀ parts,D.digest hash parts=hashv parts) (code : Code A) (before : Log) :
    CheckpointBytes5Effect.run D hash code before=
      CheckpointBytes5Effect.run (SdkC_Source.dictionary hashv) () code before := by
  induction code generalizing before with
  | done a => rfl
  | step r k ih => cases r <;> first | rfl | exact ih _ _
  | read parts k ih =>
    simp only [CheckpointBytes5Effect.run,SdkC_Source.dictionary,law]
    cases h : hashv parts <;> simp only [h,bind_tc_ok,bind_tc_fail,bind_tc_div]
    all_goals first | rfl | exact ih _ _
#print axioms run
end AspisR1.F3S_EffectDictionary
end
