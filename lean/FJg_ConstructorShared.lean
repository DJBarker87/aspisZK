import FJg_PointProvenance
import FJg_DigitEqual
import FJf_RawCircleOuterFrame
import FJc_Constructor
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJg_ConstructorShared
open Aeneas Aeneas.Std Result
open FJc_WeightQMBridge (SQ)
open FJg_DigitProvenance (cell)
/-- SAME returned constructor: the two guard digits have identical bytes
in original and absorption factor rows, without any canonicality premise. -/
theorem source (v : FIn_WeightsExtract.FInVariant) (alpha : Array SQ 10#usize)
    (z : FJf_CircleOuterBody.Z) (w : FIn_WeightsExtract.Weights)
    (run : FIn_WeightsExtract.weights_new v alpha z=ok (.Ok w))
    (d : Nat) (hd : d=2 ∨ d=3) : cell w.factors 0 d=cell w.factors 2 d := by
  obtain ⟨points,a8,a9,f1,f2,hp,h8,h9,hf1,hf2,hw⟩ := FJc_Constructor.parts v alpha z w run
  have complete := FJg_PointProvenance.three points _ f1 hf1
  have hd5 : d<5 := by rcases hd with rfl|rfl <;> decide
  obtain ⟨x,hx,sx⟩ := complete 0#usize (by decide) d hd5
  obtain ⟨y,hy,sy⟩ := complete 2#usize (by decide) d hd5
  have eq := FJg_DigitEqual.source alpha points hp d hd x y sx sy
  have fr0 := FJf_RawCircleOuterFrame.two z 0 (by decide) f1 f2 hf2
  have fr2 := FJf_RawCircleOuterFrame.two z 2 (by decide) f1 f2 hf2
  subst w
  change cell f2 0 d=cell f2 2 d
  unfold cell
  rw [fr0,fr2]
  change cell f1 0 d=cell f1 2 d
  simpa only [show (0#usize).val=0 from by decide,show (2#usize).val=2 from by decide] using
    hx.trans ((congrArg some eq).trans hy.symm)
#print axioms source
end AspisR1.FJg_ConstructorShared
end
