import RPz7_F3V_SdkPreparation
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3V_LoweredPreparation
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisR1PublicPreparation AspisR1PublicPreparation.PreparedHashCode

theorem same {Hash : Type} (H : Bytes → State)
    (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash)
    (ops : AspisR1CurrentCaller.Ops) (B : FinishModel.Boundaries)
    (std : ClaimsUnrolledFinish.StdCalls)
    (pub : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : Hash)
    (scratch : Array AspisR1CurrentCaller.aspis_core.field.wide_exact.WideExact 29#usize) :
    SdkD_PrepareLower.lower (SdkD_PrepareSource.code ops B std D pub proof hash scratch)=
      SdkD_PrepareLower.lower (SdkD_PrepareSource.code ops B std
        (F3V_OracleDictionary.current H D) pub proof hash scratch) := by
  rw [←F3V_SdkPreparation.same H D]
  exact (F3U_Rehash.lowered H _).symm

#print axioms same
end AspisR1.F3V_LoweredPreparation
end
