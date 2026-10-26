import F3S_EffectDictionary
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3S_EffectLog
open Aeneas Aeneas.Std Result AspisR1Stage2 CheckpointBytes5Effect
 theorem accepted {A Hash : Type} (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (law : ∀ parts,D.digest hash parts=hashv parts) (code : Code A) (out : A) (after : Log)
    (success : CheckpointBytes5Effect.run D hash code []=ok (out,after)) :
    SdkC_Source.readLog (SdkC_Source.run hashv code []).2=CheckpointBytes5Inputs.observe after := by
  rw [F3S_EffectDictionary.run hashv D hash law] at success
  have erased := CheckpointBytes5Effect.run_success (SdkC_Source.dictionary hashv) () code [] after out success
  have native : (SdkC_Source.run hashv code []).1=ok out := (SdkC_Source.erasure hashv code []).trans erased
  obtain ⟨other,ran,aligned⟩ := F3N_SourceEffect.accepted hashv code out [] [] rfl native
  have same : other=after := congrArg Prod.snd (Result.ok.inj (ran.symm.trans success))
  subst other
  exact aligned.symm
#print axioms accepted
end AspisR1.F3S_EffectLog
end
