import RPz7_F3S_BatchDictionary
import RPz7_GExq_FirstCode
import RPz7_F3U_FirstInstances
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
  rw [F3U_FirstInstances.native,F3U_FirstInstances.retained]
  have batch : GExq_BatchSource.current D () proof=SdkC_BatchSource.currentCode hashv proof := by
    funext p root
    exact F3S_BatchDictionary.current hashv D proof p root
  rw [batch]

#print axioms same
end AspisR1.F3U_FirstCode
end
