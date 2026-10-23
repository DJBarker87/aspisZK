import EqualityValueLoop

import AspisR1.TerminalLaneModel53

/-! Row-major decoded claims. Column 28 is not read by terminalValue; its
zero extension here makes the 84-cell source carrier explicit. -/
set_option autoImplicit false
namespace AspisR1.TerminalClaimModel53
noncomputable section
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.SemanticCompositionCoefficients
abbrev decode := AspisR1.ExtractedMaskQM31Exact.decode
abbrev Claims := Array QM 84#usize

def claims (a : Claims) (r : Fin 3) (c : Fin 29) : ExactQM :=
  if h : c.val < 28 then
    decode (a.val[r.val*28+c.val]'(by have := r.isLt; simpa [a.property] using (show r.val*28+c.val<84 by omega)))
  else 0

def openings (a : Claims) : R0P.Openings ExactQM :=
  ⟨fun c => claims a 0 (Fin.castLE (by omega) c),
   fun c => claims a 1 (Fin.castLE (by omega) c),
   fun c => claims a 2 (Fin.castLE (by omega) c)⟩

theorem openings_eq (a : Claims) (o : Openings)
    (hz : ∀ i : Fin 16, o.z.val[i.val]'(by simpa [o.z.property] using i.isLt) =
      a.val[i.val]'(by have := i.isLt; simpa [a.property] using (show i.val<84 by omega)))
    (hs : ∀ i : Fin 16, o.succ_z.val[i.val]'(by simpa [o.succ_z.property] using i.isLt) =
      a.val[28+i.val]'(by have := i.isLt; simpa [a.property] using (show 28+i.val<84 by omega)))
    (hx : ∀ i : Fin 16, o.xor12_z.val[i.val]'(by simpa [o.xor12_z.property] using i.isLt) =
      a.val[56+i.val]'(by have := i.isLt; simpa [a.property] using (show 56+i.val<84 by omega))) :
    exactOpenings o = openings a := by
  unfold exactOpenings AspisR1.SelectorValueLanePreprocessRangeValues.exactOpenings openings
  congr 1
  · funext i
    simp only [exactOpenings,AspisR1.SelectorValueLanePreprocessRangeValues.exactOpenings,
      openings,claims,Fin.val_castLE,show i.val<28 by omega,dif_pos,Fin.val_zero,zero_mul,zero_add,hz]
  · funext i
    simp only [exactOpenings,AspisR1.SelectorValueLanePreprocessRangeValues.exactOpenings,
      openings,claims,Fin.val_castLE,show i.val<28 by omega,dif_pos,hs]
    rfl
  · funext i
    simp only [exactOpenings,AspisR1.SelectorValueLanePreprocessRangeValues.exactOpenings,
      openings,claims,Fin.val_castLE,show i.val<28 by omega,dif_pos,hx]
    rfl

theorem decodedPoint_eq (a : Array QM 10#usize) :
    AspisR1.EqualityValueLoop.decodedArray a = AspisR1.SelectorMarginalModel.modelPoint a := by
  funext i
  simp only [AspisR1.EqualityValueLoop.decodedArray,AspisR1.SelectorMarginalModel.modelPoint,
    AspisR1.SelectorAtPointModel.exactPoint,i.isLt,dif_pos]
  rfl

#print axioms openings_eq
#print axioms decodedPoint_eq
end
end AspisR1.TerminalClaimModel53
