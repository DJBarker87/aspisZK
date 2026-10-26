import GExq_CodeTrace
set_option autoImplicit false
namespace AspisR1.F3R_SdkPure
open Aeneas Aeneas.Std Result CheckpointBytes5Effect

theorem right {A B : Type} (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (r : Result A) (k : A → Code B) (out : B)
    (success : erase (SdkC_Source.dictionary hashv) () (bind (liftResult r) k)=ok out) :
    ∃ a,r=ok a ∧ erase (SdkC_Source.dictionary hashv) () (k a)=ok out ∧
      SdkC_Source.readLog (SdkC_Source.run hashv (bind (liftResult r) k) []).2=
        SdkC_Source.readLog (SdkC_Source.run hashv (k a) []).2 := by
  cases r with
  | ok a=>exact ⟨a,rfl,success,rfl⟩
  | fail e=>cases success
  | div=>cases success

#print axioms right
end AspisR1.F3R_SdkPure
