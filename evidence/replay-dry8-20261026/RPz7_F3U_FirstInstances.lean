import RPz7_GExq_FirstCode
import RPz7_F3U_FirstSkeleton
import RPz7_GExp_FirstCode
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3U_FirstInstances
open Aeneas Aeneas.Std Result AspisR1CurrentCaller

theorem native (base : Ops)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (D : aspis_core.digest.Digest32 Unit)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (physical proof : Slice U8) (split : Usize) :
    GExq_FirstCode.code base B std hashv D pub physical proof split ()=
      F3U_FirstSkeleton.code base B std hashv D pub physical proof split
        (GExq_BatchSource.current D () proof) := rfl
#print axioms native

theorem retained (base : Ops)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (D : aspis_core.digest.Digest32 Unit)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (physical proof : Slice U8) (split : Usize) :
    GExp_FirstCode.code base B std hashv D pub physical proof split=
      F3U_FirstSkeleton.code base B std hashv D pub physical proof split
        (SdkC_BatchSource.currentCode hashv proof) := rfl
#print axioms retained
end AspisR1.F3U_FirstInstances
end
