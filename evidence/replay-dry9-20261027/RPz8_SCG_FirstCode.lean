import RPz8_SCG_BatchCode
import RPz7_GExq_FirstCode
import RPz7_DrvC_Flow
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCG_FirstCode
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open CheckpointBytes5Effect

/-- Same typed digest, including all reject branches, before comparing the
outer account carrier. This does not use native/source erasure. -/
theorem code (base : Ops)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (D : aspis_core.digest.Digest32 Unit)
    (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (split : Usize) :
    GExq_FirstCode.code base B std hashv D semantic pub proof split () =
      GExp_FirstCode.code base B std hashv D semantic pub proof split := by
  unfold GExq_FirstCode.code GExp_FirstCode.code
  simp only [SCG_BatchCode.current D () hashv]
  rfl

#print axioms code
end AspisR1.SCG_FirstCode
end
