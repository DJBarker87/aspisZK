import F3S_BatchDictionary
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3V_BatchDictionary
open Aeneas Aeneas.Std Result

theorem current (first second : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (proof : Slice U8) (p : AspisR1CurrentCaller.verifier.Prepared) (root : Array U8 32#usize) :
    SdkC_BatchSource.currentCode first proof p root=SdkC_BatchSource.currentCode second proof p root := by
  rw [←F3S_BatchDictionary.current first (SdkC_CurrentInstall.toCurrent (SdkC_Source.dictionary first))]
  exact F3S_BatchDictionary.current second _ _ _ _

#print axioms current
end AspisR1.F3V_BatchDictionary
end
