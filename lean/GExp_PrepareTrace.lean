import GExp_LowerTrace
set_option autoImplicit false
noncomputable section
namespace AspisR1.GExp_PrepareTrace
open Aeneas Aeneas.Std Result AspisR1CurrentCaller

theorem source_log (sdk : AdapterRw.Ops)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction sdk native1 native2 hashv)
    (ops : Ops) (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (std : ClaimsUnrolledFinish.StdCalls)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : AdapterRw.SolanaDigest)
    (input : Array aspis_core.field.wide_exact.WideExact 29#usize) :
    SdkC_Source.readLog (SdkC_Source.run hashv (SdkD_PrepareLower.lower
      (SdkD_PrepareSource.code ops B std (GExp_InstalledPrepare.digest sdk) pub proof hash input)) []).2 =
    AspisR1PublicPreparation.PreparedHashCode.observe
      (AspisR1PublicPreparation.PreparedHashCode.run
        (SdkD_PrepareSource.code ops B std (GExp_InstalledPrepare.digest sdk) pub proof hash input)).1 :=
  GExp_LowerTrace.log hashv _
    (GExp_InstalledPrepare.associated sdk native1 native2 hashv extraction ops B std pub proof hash input)

#print axioms source_log
end AspisR1.GExp_PrepareTrace
end
