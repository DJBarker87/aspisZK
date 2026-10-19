import R0P.MaskBadSets

/-! Replacing only the stored extra-opening vector preserves the older
semantic-prefix classifier and C2 word construction. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.SemanticContext

open R0P R0P.Mask R0P.SemSource AspisWide.InitialEncoder
  AspisPool.AlgorithmicCircleDecoderV7

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K]

def withExtra {S : Fin 29 → Subfield K} (x : TypedContext K S)
    (extra : Fin 29 → K) : TypedContext K S :=
  { x with extraClaims := extra }

theorem c2Words_withExtra {S : Fin 29 → Subfield K} (x : TypedContext K S)
    (extra : Fin 29 → K) (h g : InitialWord K) :
    c2Words (withExtra x extra) h g = c2Words x h g := by
  rfl

theorem semanticBadZ_withExtra {S : Fin 29 → Subfield K} {F : Subfield K}
    (maskClaims : (Fin 29 → K) → (Fin 29 → K) → (Fin 10 → K) → K)
    (B : PackBasis F) (x : TypedContext K S) (extra : Fin 29 → K)
    (rounds : List (MsgZ K × ChalZ K)) (sm : SemMsgZ K) (c : K) :
    semanticBadZ maskClaims B ⟨withExtra x extra, rounds⟩ sm c ↔
      semanticBadZ maskClaims B ⟨x, rounds⟩ sm c := by
  rfl

#print axioms c2Words_withExtra
#print axioms semanticBadZ_withExtra

end AspisR1.SemanticContext
end
