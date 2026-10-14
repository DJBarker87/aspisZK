import R1SemanticContext
import R1SemanticHit

/-! The parsed first-25-row no-hit event is unchanged when only the legacy
extra-opening vector is replaced. This does not change an opening decision
or assert a shared-oracle law. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.SemanticContext
open R0P R0P.Mask R0P.SemSource R0C.SemStatement

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K]

theorem no_hitFrom_withExtra_iff
    {S : Fin 29 → Subfield K} {F : Subfield K}
    (x : TypedContext K S) (extra : Fin 29 → K)
    (fallback : AspisR0.ChordGeometry.Point K)
    (maskClaims : (Fin 29 → K) → (Fin 29 → K) → (Fin 10 → K) → K)
    (B : PackBasis F) (rs : List (MsgZ K × ChalZ K)) (cs : List K)
    (hparse : semChalsZ rs = some cs) (hlen : rs.length ≤ 25) :
    (¬ hitFrom (sourceDataWithFallbackZ fallback maskClaims B) (withExtra x extra) [] rs) ↔
      (¬ hitFrom (sourceDataWithFallbackZ fallback maskClaims B) x [] rs) := by
  rw [SemanticHit.no_hitFrom_iff_all_semanticBadZ_excluded
    (withExtra x extra) fallback maskClaims B rs cs hparse hlen,
    SemanticHit.no_hitFrom_iff_all_semanticBadZ_excluded
      x fallback maskClaims B rs cs hparse hlen]
  simp only [semanticBadZ_withExtra]

#print axioms no_hitFrom_withExtra_iff
end AspisR1.SemanticContext
end
