import FoldInversesRefinement
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1FoldInverses.Refinement
variable {K : Type} [Field K] [Algebra (ZMod P) K]

theorem circle_model_success (ops : FoldOps) (canonical : E → Prop) (decode : E → K)
    (R : OperationsRefine ops canonical decode) (alpha a b c d out : E)
    (ix iy lx ly lz : B)
    (Ca : canonical a) (Cb : canonical b) (Cc : canonical c) (Cd : canonical d)
    (Calpha : canonical alpha)
    (Cix : CanonicalBase ix) (Ciy : CanonicalBase iy)
    (h : verifier.circle_fold_with_inverses ops alpha (Array.make 4#usize [a,b,c,d])
      (Array.make 5#usize [ix,iy,lx,ly,lz]) = .ok out) :
    canonical out ∧ decode out = AspisV5ComponentCConcreteFoldLinearity.circleFoldValue (decode alpha)
      (algebraMap (ZMod P) K (R1ZCircleFoldMathV1.rustHalf * decodeBase ix))
      (algebraMap (ZMod P) K (R1ZCircleFoldMathV1.rustHalf * decodeBase iy))
      (values4 (decode a) (decode b) (decode c) (decode d)) := by
  obtain ⟨Cout,hvalue⟩ := circle_success ops canonical decode R alpha a b c d out ix iy lx ly lz Ca Cb Cc Cd Calpha Cix Ciy h
  refine ⟨Cout,hvalue.trans ?_⟩
  exact R1ZCircleFoldMathV1.sourceCircleFold_eq_model _ _ _ _
#print axioms circle_model_success

theorem line_model_success (ops : FoldOps) (canonical : E → Prop) (decode : E → K)
    (R : OperationsRefine ops canonical decode) (alpha a b c d out : E)
    (ix iy lx ly lz : B)
    (Ca : canonical a) (Cb : canonical b) (Cc : canonical c) (Cd : canonical d)
    (Calpha : canonical alpha)
    (Clx : CanonicalBase lx) (Cly : CanonicalBase ly) (Clz : CanonicalBase lz)
    (h : verifier.line_fold_with_inverses ops alpha (Array.make 4#usize [a,b,c,d])
      (Array.make 5#usize [ix,iy,lx,ly,lz]) = .ok out) :
    canonical out ∧ decode out = AspisV5ComponentCConcreteFoldLinearity.lineFoldValue (decode alpha)
      (algebraMap (ZMod P) K (R1ZCircleFoldMathV1.rustHalf * decodeBase lx))
      (-(algebraMap (ZMod P) K (R1ZCircleFoldMathV1.rustHalf * decodeBase ly)))
      (algebraMap (ZMod P) K (R1ZCircleFoldMathV1.rustHalf * decodeBase lz))
      (values4 (decode a) (decode b) (decode c) (decode d)) := by
  obtain ⟨Cout,hvalue⟩ := line_success ops canonical decode R alpha a b c d out ix iy lx ly lz Ca Cb Cc Cd Calpha Clx Cly Clz h
  refine ⟨Cout,hvalue.trans ?_⟩
  exact R1ZCircleFoldMathV1.sourceLineFold_eq_model _ _ _ _ _
#print axioms line_model_success
end AspisR1FoldInverses.Refinement
