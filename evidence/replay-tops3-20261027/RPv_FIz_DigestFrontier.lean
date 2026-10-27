import RPv_FIz_EmptyRight
import RPv_FIz_DigestRead
import RPv_FIw_PublicModel
import R0P.Digest
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIz_DigestFrontier
open Aeneas Aeneas.Std
open FIv_NativeValue (K)
open FIw_PublicModel (Public Openings Selectors)
theorem read (p : Public) (level : Fin 20) (j : Fin 8) :
    FIw_PublicModel.digest (FIy_FrontierMeaning.frontier p.transition.live_snapshot level.val) j=
      (FIw_PublicModel.ofPublic p).snapshotFrontier level j := by
  unfold FIy_FrontierMeaning.frontier FIw_PublicModel.ofPublic
  rw [List.getElem?_eq_getElem (by rw [p.transition.live_snapshot.frontier.property];exact level.isLt)]
  rfl

theorem value (p : Public) (o : Openings) (s : Selectors) (level : Fin 20) (j : Fin 8) :
    FIy_FrontierMeaning.increment p.transition.live_snapshot s o.z level.val j.val=
      FIw_PublicModel.selector s (R0P.digestRow (FIw_PublicModel.ofPublic p) (.frontier level))*
        ((FIw_PublicModel.openings o).z ⟨(R0P.digestStart (FIw_PublicModel.ofPublic p) (.frontier level)).val+j.val,by omega⟩-
          R0P.digestTarget (FIw_PublicModel.ofPublic p) (.frontier level) j) := by
  unfold FIy_FrontierMeaning.increment
  by_cases hz : FIy_FrontierMeaning.zero p.transition.live_snapshot level.val
  · rw [if_pos hz,FIz_EmptyRight.value level j]
    simp only [R0P.digestRow,R0P.digestStart,R0P.digestTarget,show R0P.digestBitZero (FIw_PublicModel.ofPublic p) level from hz,↓reduceIte]
    simp only [R0P.digestBitZero,FIw_PublicModel.ofPublic] at *
    simp only [FIy_FrontierMeaning.zero] at hz
    simp only [hz,↓reduceIte,R0P.g2Row,FIw_PublicModel.selector,FIy_FrontierMeaning.rowValue,
      FIw_PublicModel.openings,show (0 : Fin 16).val=0 from rfl,show (8 : Fin 9).val=8 from rfl,Nat.add_zero,Nat.mul_comm]
  · rw [if_neg hz,FIz_DigestRead.value,read]
    simp only [R0P.digestRow,R0P.digestStart,R0P.digestTarget,show ¬R0P.digestBitZero (FIw_PublicModel.ofPublic p) level from hz,↓reduceIte]
    simp only [R0P.g2Row,FIw_PublicModel.selector,FIy_FrontierMeaning.rowValue,
      FIw_PublicModel.openings,show (12 : Fin 16).val=12 from rfl,show (0 : Fin 9).val=0 from rfl,Nat.zero_add,Nat.mul_comm]
#print axioms read
#print axioms value
end AspisR1.FIz_DigestFrontier
end
