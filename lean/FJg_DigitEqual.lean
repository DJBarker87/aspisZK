import FJg_SharedPoints
import FJg_DigitProvenance
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJg_DigitEqual
open Aeneas Aeneas.Std Result
open FJc_WeightQMBridge (SQ)
open FJg_DigitProvenance (Source Digit)

theorem coordinates (d : Nat) (hd : d=2 ∨ d=3) :
    9-2*FJf_PointIndices.tau d≠6 ∧ 9-2*FJf_PointIndices.tau d≠7 ∧
    8-2*FJf_PointIndices.tau d≠6 ∧ 8-2*FJf_PointIndices.tau d≠7 := by
  rcases hd with rfl|rfl <;> decide

/-- Exact factor bytes agree, from the SAME installed point constructor's
unchanged coordinates; no field-value injectivity assumption is needed. -/
theorem source (alpha : Array SQ 10#usize) (points : FJf_PointBody.Points)
    (run : FIn_WeightsExtract.state_only_prefix.r0.statement_points alpha=ok points)
    (d : Nat) (hd : d=2 ∨ d=3) (x y : Digit)
    (hx : Source points 0 d x) (hy : Source points 2 d y) : x=y := by
  obtain ⟨p,p',q,q',v,v',hp2,hq,hv,hp,hq',hv',hp',frame⟩ := FJg_SharedPoints.source alpha points run
  have hp0 := FJf_OriginalPoint.value alpha points run
  obtain ⟨px,a,b,f0,f1,f2,f3,hpx,ha,hb,href,rfl⟩ := hx
  obtain ⟨py,a',b',g0,g1,g2,g3,hpy,ha',hb',href',rfl⟩ := hy
  have ex : px=alpha := Option.some.inj (hpx.symm.trans (FJc_ReadSlot.slot _ _ _ hp0))
  have ey : py=p' := Option.some.inj (hpy.symm.trans (FJc_ReadSlot.slot _ _ _ hp2))
  subst px
  subst py
  have coords := coordinates d hd
  have ea : a'=a := Option.some.inj (ha'.symm.trans ((frame _ coords.1 coords.2.1).trans ha))
  have eb : b'=b := Option.some.inj (hb'.symm.trans ((frame _ coords.2.2.1 coords.2.2.2).trans hb))
  subst a'
  subst b'
  have same := Result.ok.inj (href.symm.trans href')
  have es : f0=g0 ∧ f1=g1 ∧ f2=g2 ∧ f3=g3 := by simpa only [List.cons.injEq,and_true] using same
  rcases es with ⟨rfl,rfl,rfl,rfl⟩
  rfl
#print axioms coordinates
#print axioms source
end AspisR1.FJg_DigitEqual
end
