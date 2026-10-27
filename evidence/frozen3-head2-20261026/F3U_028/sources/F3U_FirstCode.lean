import F3S_BatchDictionary
import GExq_FirstCode
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3U_FirstCode
open Aeneas Aeneas.Std Result AspisR1CurrentCaller

theorem same (base : Ops)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (D : aspis_core.digest.Digest32 Unit)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (physical proof : Slice U8) (split : Usize) :
    GExq_FirstCode.code base B std hashv D pub physical proof split ()=
      GExp_FirstCode.code base B std hashv D pub physical proof split := by
  simp only [GExq_FirstCode.code,GExp_FirstCode.code,F3S_BatchDictionary.current]

#print axioms same
end AspisR1.F3U_FirstCode
end
