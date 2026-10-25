import S1CurrentPrepareCodeExactV1
import RowShape_InstalledSlots
import SdkD_PrepareLower
set_option autoImplicit false
noncomputable section
namespace AspisR1.SdkD_PrepareSource
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open AspisR1PublicPreparation.PreparedHashCode

/-- The complete source preparation tree for the exact existing installation.
Both semantic verification and original preparation expose their hash calls. -/
def code (ops : Ops)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    {H : Type} (D : aspis_core.digest.Digest32 H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : H)
    (input : Array aspis_core.field.wide_exact.WideExact 29#usize) :=
  S1PrepareCode.prepare ops AspisS1ExtractedRoundChildren.children
    (ClaimsUnrolledFinish.install std B) D pub proof hash input

/-- All outer fail/div and inner rejection outcomes, not merely accepted outputs. -/
theorem source (ops : Ops)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    {H : Type} (D : aspis_core.digest.Digest32 H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : H)
    (input : Array aspis_core.field.wide_exact.WideExact 29#usize) :
    erase (code ops B std D pub proof hash input) =
      verifier.candidate.prepare (RowShape_InstalledSlots.verifierOps ops B std)
        D pub proof hash none input :=
  S1PrepareCode.source ops AspisS1ExtractedRoundChildren.children
    (ClaimsUnrolledFinish.install std B) D pub proof hash input

/-- The interpreter's ordered attempt log and returned scratch come from this
same source tree. No supplied trace or independently selected child is used. -/
theorem source_run (ops : Ops)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    {H : Type} (D : aspis_core.digest.Digest32 H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : H)
    (input : Array aspis_core.field.wide_exact.WideExact 29#usize) :
    (run (code ops B std D pub proof hash input)).2 =
      verifier.candidate.prepare (RowShape_InstalledSlots.verifierOps ops B std)
        D pub proof hash none input := by
  rw [run_value,source]

#print axioms source
#print axioms source_run
end AspisR1.SdkD_PrepareSource
end
