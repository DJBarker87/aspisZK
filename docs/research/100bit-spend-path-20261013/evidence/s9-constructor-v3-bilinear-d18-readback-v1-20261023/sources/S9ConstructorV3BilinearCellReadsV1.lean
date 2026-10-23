import S9ConstructorV3StatementCellSemanticsV1
import R1D18PointWeights

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9ConstructorV3BilinearCellReadsV1
open AspisR1S9ConstructorV3Loop2InnerCanonicalV1
open AspisR1S9ConstructorV3QMMulSemanticsV1

/-- Small readback bridge from the four proved source values to the retained
D18 pairFactor model, inspecting four scalar array slots only. -/
theorem make4_read_pairFactor
    (a b q0 q1 q2 q3 : Q)
    (h0 : decode q0 = (1-decode a)*(1-decode b))
    (h1 : decode q1 = decode a*(1-decode b))
    (h2 : decode q2 = (1-decode a)*decode b)
    (h3 : decode q3 = decode a*decode b)
    (i : Usize) (q : Q)
    (hread : Array.index_usize (Array.make 4#usize [q0,q1,q2,q3] : Cell) i = .ok q) :
    decode q = AspisR1.pairFactor (decode a) (decode b) i.val := by
  have hi : i.val < 4 := index_success_bound _ _ _ hread
  have hcases : i.val=0 ∨ i.val=1 ∨ i.val=2 ∨ i.val=3 := by omega
  rcases hcases with hzero | hone | htwo | hthree
  · have he : i=0#usize := UScalar.eq_of_val_eq hzero
    subst i
    unfold Array.index_usize at hread
    change Result.ok q0 = Result.ok q at hread
    have hq : q0=q := Result.ok.inj hread
    subst q
    simpa [AspisR1.pairFactor] using h0
  · have he : i=1#usize := UScalar.eq_of_val_eq hone
    subst i
    unfold Array.index_usize at hread
    change Result.ok q1 = Result.ok q at hread
    have hq : q1=q := Result.ok.inj hread
    subst q
    simpa [AspisR1.pairFactor] using h1
  · have he : i=2#usize := UScalar.eq_of_val_eq htwo
    subst i
    unfold Array.index_usize at hread
    change Result.ok q2 = Result.ok q at hread
    have hq : q2=q := Result.ok.inj hread
    subst q
    simpa [AspisR1.pairFactor] using h2
  · have he : i=3#usize := UScalar.eq_of_val_eq hthree
    subst i
    unfold Array.index_usize at hread
    change Result.ok q3 = Result.ok q at hread
    have hq : q3=q := Result.ok.inj hread
    subst q
    simpa [AspisR1.pairFactor] using h3

#print axioms make4_read_pairFactor
end AspisR1S9ConstructorV3BilinearCellReadsV1
