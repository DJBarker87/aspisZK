import NBL_QueryDictionary
import S1ClosedPreparationHashCodeV1
set_option autoImplicit false
noncomputable section
namespace AspisR1.NBL_CohortCode
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisR1CurrentCaller.BorrowedClaimPrepared

/-- The exact adopted hash-code dictionary; no alternative preparation body. -/
theorem dictionary :
    PreparedHashCode.withQueries NBA_Installed.actual NBL_QueryDictionary.boundaries=NBA_Installed.actual := by
  have b : NBA_Installed.actual=closedHashBoundaries := rfl
  have q : NBL_QueryDictionary.boundaries=closedHashQueries := rfl
  rw [b,q]
  exact closedHashBoundaries_queries

def code {H : Type} (D : aspis_core.Digest32 H)
    (sem : r1_semantic.Verified H) (view : verifier.View) (hash : H)
    (old : Array aspis_core.field.WideExact 29#usize) :=
  PreparedSourceEffects.prepare
    (PreparedHashCode.preparationEffects NBA_Installed.actual NBL_QueryDictionary.boundaries)
    D sem view hash old

/-- Every Result constructor, with no successful call or supplied whole result. -/
theorem erasure {H : Type} (D : aspis_core.Digest32 H)
    (sem : r1_semantic.Verified H) (view : verifier.View) (hash : H)
    (old : Array aspis_core.field.WideExact 29#usize) :
    PreparedHashCode.erase (code D sem view hash old)=
      PreparedScratchModel.prepare NBA_Installed.actual D sem view hash old := by
  rw [code,PreparedHashCode.preparation_erasure,dictionary,OriginalPreparedNative.eq_prepare]

#print axioms dictionary
#print axioms erasure
end AspisR1.NBL_CohortCode
end
