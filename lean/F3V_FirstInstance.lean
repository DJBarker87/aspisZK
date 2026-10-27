import F3V_FirstTemplate
import F3U_FirstInstances
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3V_FirstInstance
open Aeneas Aeneas.Std Result AspisR1CurrentCaller

theorem same (base : Ops)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (D : aspis_core.digest.Digest32 Unit)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (physical proof : Slice U8) (split : Usize) :
    GExp_FirstCode.code base B std hashv D pub physical proof split=
      F3V_FirstTemplate.code base B std pub physical proof split
        (fun g=> SdkD_PrepareLower.lower (SdkD_PrepareSource.code
          (Op5T_Concrete.current {base with op16:=Tx1Q_Install.writer}) B std D pub proof () g))
        (SdkC_BatchSource.currentCode hashv proof) := rfl

#print axioms same
end AspisR1.F3V_FirstInstance
end
