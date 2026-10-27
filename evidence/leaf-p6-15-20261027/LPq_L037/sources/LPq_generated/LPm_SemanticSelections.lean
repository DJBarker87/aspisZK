import CurrentClaimScalarBody
set_option autoImplicit false
namespace AspisR1.LPm_SemanticSelections
open Aeneas Aeneas.Std Result AspisR1CurrentPreparedClaim

/-- Exact source array/index routing, including its Result failures. No
canonicality or supplied scalar-read observation is needed. -/
theorem claims {Dot Hash : Type} (ops : ClaimDotOps Dot) (sem : r1_semantic.Verified Hash)
    (y1 : Slice U8) (point lane : Usize) (hp : point.val<3) :
    ClaimScalar.read ops sem y1 point lane =
      (do let row ← Array.index_usize sem.claims point; Array.index_usize row lane) := by
  have small : point≤2#usize := by scalar_tac
  simp only [ClaimScalar.read,if_pos small]

theorem extra {Dot Hash : Type} (ops : ClaimDotOps Dot) (sem : r1_semantic.Verified Hash)
    (y1 : Slice U8) (point lane : Usize) (hp : point.val=3) :
    ClaimScalar.read ops sem y1 point lane = Array.index_usize sem.extra lane := by
  have large : ¬point≤2#usize := by scalar_tac
  simp only [ClaimScalar.read,if_neg large,hp]

theorem before_z1 {Dot Hash : Type} (ops : ClaimDotOps Dot) (sem : r1_semantic.Verified Hash)
    (y1 : Slice U8) (point lane : Usize) (hp : point.val=4) :
    ClaimScalar.read ops sem y1 point lane = Array.index_usize sem.before_z1 lane := by
  have large : ¬point≤2#usize := by scalar_tac
  simp only [ClaimScalar.read,if_neg large,hp]

#print axioms claims
#print axioms extra
#print axioms before_z1
end AspisR1.LPm_SemanticSelections
