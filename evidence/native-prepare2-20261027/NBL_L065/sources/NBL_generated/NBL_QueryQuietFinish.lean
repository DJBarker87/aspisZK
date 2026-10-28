import NBL_QueryEffectFactor
import NBL_QuietRun
set_option autoImplicit false
namespace AspisR1.NBL_QueryQuietFinish
open Aeneas Aeneas.Std Result AspisR1PublicPreparation PreparedHashCode

/-- The pure decoder/embedding suffix has no digest attempts, for ALL Results. -/
theorem source (B : QueriesModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
    (self : transcript.Transcript H)
    (blocks advances : Array (Array U8 32#usize) 8#usize) :
    run (NBL_QueryEffectFactor.finish B D self blocks advances)=
      ([],NBA_QueryFactor.finishQuery B D self blocks advances) := by
  unfold NBL_QueryEffectFactor.finish NBA_QueryFactor.finishQuery
  repeat' first
    | (apply NBL_QuietRun.bind; intro x)
    | rfl
    | split

#print axioms source
end AspisR1.NBL_QueryQuietFinish
