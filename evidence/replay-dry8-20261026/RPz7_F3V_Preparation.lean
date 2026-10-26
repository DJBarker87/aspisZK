import RPz7_F3V_CurrentSemantic
import RPz7_F3V_ClosedPreparation
import RPz7_F3V_RehashCongr
import RPz7_S1CurrentPrepareCodeExactV1
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3V_Preparation
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisR1PublicPreparation AspisR1PublicPreparation.PreparedHashCode

theorem same {Hash : Type} (H : Bytes → State)
    (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash)
    (base : AspisR1CurrentCaller.Ops) (R : RoundModel.Boundaries) (B : FinishModel.Boundaries)
    (pub : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : Hash)
    (scratch : Array AspisR1CurrentCaller.aspis_core.field.wide_exact.WideExact 29#usize) :
    F3U_Rehash.code H (AspisR1CurrentCaller.S1PrepareCode.prepare base R B D pub proof hash scratch)=
      AspisR1CurrentCaller.S1PrepareCode.prepare base R B (F3V_OracleDictionary.current H D) pub proof hash scratch := by
  unfold AspisR1CurrentCaller.S1PrepareCode.prepare
  repeat' first
    | (solve | with_reducible apply F3V_CurrentSemantic.same)
    | (solve | with_reducible apply F3V_ClosedPreparation.same)
    | with_reducible apply F3V_RehashCongr.bind
    | intro x
    | (solve | rfl)
    | split

#print axioms same
end AspisR1.F3V_Preparation
end
