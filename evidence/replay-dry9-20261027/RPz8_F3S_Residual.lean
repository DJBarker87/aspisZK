import RPz8_F3R_SdkPure
set_option autoImplicit false
namespace AspisR1.F3S_Residual
open Aeneas Aeneas.Std Result CheckpointBytes5Effect
 theorem impossible {A E : Type} (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (e : E) (out : A)
    (h : erase (SdkC_Source.dictionary hashv) ()
      (liftResult (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        A (core.convert.FromSame E) (core.result.Result.Err e)))=ok (.Ok out)) : False := by
  cases h
#print axioms impossible
end AspisR1.F3S_Residual
