import CurrentClaimScalarBody
set_option autoImplicit false
namespace AspisR1.LPm_SemanticSelections
open Aeneas Aeneas.Std Result AspisR1CurrentPreparedClaim

theorem claims {Dot Hash : Type} (ops : ClaimDotOps Dot) (sem : r1_semantic.Verified Hash)
    (y1 : Slice U8) (point lane : Usize) (hp : point.val<3) (hl : lane.val<29) :
    ClaimScalar.read ops sem y1 point lane =
      ok ((sem.claims.val[point.val]'(by simpa [sem.claims.property] using hp)).val[lane.val]'
        (by simpa [(sem.claims.val[point.val]'(by simpa [sem.claims.property] using hp)).property] using hl)) := by
  have small : point≤2#usize := by scalar_tac
  have prow : point.val<sem.claims.val.length := by simpa only [sem.claims.property] using hp
  have plane : lane.val<(sem.claims.val[point.val]'prow).val.length := by
    have n : (sem.claims.val[point.val]'prow).val.length=29 := (sem.claims.val[point.val]'prow).property
    omega
  simp only [ClaimScalar.read,if_pos small,Array.index_usize,
    List.getElem?_eq_getElem prow,bind_tc_ok,List.getElem?_eq_getElem plane]

theorem extra {Dot Hash : Type} (ops : ClaimDotOps Dot) (sem : r1_semantic.Verified Hash)
    (y1 : Slice U8) (point lane : Usize) (hp : point.val=3) (hl : lane.val<29) :
    ClaimScalar.read ops sem y1 point lane =
      ok (sem.extra.val[lane.val]'(by simpa [sem.extra.property] using hl)) := by
  have large : ¬point≤2#usize := by scalar_tac
  have plane : lane.val<sem.extra.val.length := by simpa only [sem.extra.property] using hl
  simp only [ClaimScalar.read,if_neg large,hp,Array.index_usize,List.getElem?_eq_getElem plane]

theorem before_z1 {Dot Hash : Type} (ops : ClaimDotOps Dot) (sem : r1_semantic.Verified Hash)
    (y1 : Slice U8) (point lane : Usize) (hp : point.val=4) (hl : lane.val<29) :
    ClaimScalar.read ops sem y1 point lane =
      ok (sem.before_z1.val[lane.val]'(by simpa [sem.before_z1.property] using hl)) := by
  have large : ¬point≤2#usize := by scalar_tac
  have plane : lane.val<sem.before_z1.val.length := by simpa only [sem.before_z1.property] using hl
  simp only [ClaimScalar.read,if_neg large,hp,Array.index_usize,List.getElem?_eq_getElem plane]

#print axioms claims
#print axioms extra
#print axioms before_z1
end AspisR1.LPm_SemanticSelections
