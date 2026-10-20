import CurrentFoldArithmeticProduct
import CurrentWideMulM31V13
import FoldInversesModel
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1CurrentWide.Proof

theorem current_fold_scale (x z : FoldE) (s : U32) (hx : CanonicalFold x)
    (h : currentFoldOps.scale x s = .ok z) :
    CanonicalFold z ∧ decodeFold z = decodeFold x *
      algebraMap (ZMod AspisR1FoldInverses.Refinement.P) AspisWideTower.WideExact
        (AspisR1FoldInverses.Refinement.decodeBase s) := by
  change runScale x s = .ok z at h
  unfold runScale at h
  cases ho : field.wide_exact.WideExact.mul_m31 (ofFoldE x) s with
  | fail e => simp only [ho,bind_tc_fail] at h; cases h
  | div => simp only [ho,bind_tc_div] at h; cases h
  | ok out =>
    simp only [ho,bind_tc_ok] at h
    have hz : toFoldE out=z := Result.ok.inj h
    have hr := wide_mul_m31_success_algebraMap (ofFoldE x) out s hx ho
    change CanonicalWide (ofFoldE z) ∧ decodeWide (ofFoldE z) = decodeWide (ofFoldE x) * _
    rw [←hz,of_to_fold]
    exact hr

theorem current_operations_refine :
    AspisR1FoldInverses.Refinement.OperationsRefine currentFoldOps CanonicalFold decodeFold where
  add := current_fold_add
  sub := current_fold_sub
  mul := current_fold_mul
  scale := by
    intro x y z hx _ h
    exact current_fold_scale x z y hx h
  baseMul := by
    intro x y z _ _ h
    exact current_fold_baseMul x y z h

theorem concrete_circle_model_success (alpha a b c d out : FoldE)
    (ix iy lx ly lz : U32)
    (Ca : CanonicalFold a) (Cb : CanonicalFold b)
    (Cc : CanonicalFold c) (Cd : CanonicalFold d) (Calpha : CanonicalFold alpha)
    (Cix : AspisR1FoldInverses.Refinement.CanonicalBase ix)
    (Ciy : AspisR1FoldInverses.Refinement.CanonicalBase iy)
    (h : AspisR1FoldInverses.verifier.circle_fold_with_inverses currentFoldOps alpha
      (Array.make 4#usize [a,b,c,d]) (Array.make 5#usize [ix,iy,lx,ly,lz]) = .ok out) :
    CanonicalFold out ∧ decodeFold out =
      AspisV5ComponentCConcreteFoldLinearity.circleFoldValue (decodeFold alpha)
        (algebraMap (ZMod AspisR1FoldInverses.Refinement.P) AspisWideTower.WideExact
          (R1ZCircleFoldMathV1.rustHalf * AspisR1FoldInverses.Refinement.decodeBase ix))
        (algebraMap (ZMod AspisR1FoldInverses.Refinement.P) AspisWideTower.WideExact
          (R1ZCircleFoldMathV1.rustHalf * AspisR1FoldInverses.Refinement.decodeBase iy))
        (AspisR1FoldInverses.Refinement.values4 (decodeFold a) (decodeFold b) (decodeFold c) (decodeFold d)) := by
  exact AspisR1FoldInverses.Refinement.circle_model_success currentFoldOps CanonicalFold decodeFold
    current_operations_refine alpha a b c d out ix iy lx ly lz Ca Cb Cc Cd Calpha Cix Ciy h

theorem concrete_line_model_success (alpha a b c d out : FoldE)
    (ix iy lx ly lz : U32)
    (Ca : CanonicalFold a) (Cb : CanonicalFold b)
    (Cc : CanonicalFold c) (Cd : CanonicalFold d) (Calpha : CanonicalFold alpha)
    (Clx : AspisR1FoldInverses.Refinement.CanonicalBase lx)
    (Cly : AspisR1FoldInverses.Refinement.CanonicalBase ly)
    (Clz : AspisR1FoldInverses.Refinement.CanonicalBase lz)
    (h : AspisR1FoldInverses.verifier.line_fold_with_inverses currentFoldOps alpha
      (Array.make 4#usize [a,b,c,d]) (Array.make 5#usize [ix,iy,lx,ly,lz]) = .ok out) :
    CanonicalFold out ∧ decodeFold out =
      AspisV5ComponentCConcreteFoldLinearity.lineFoldValue (decodeFold alpha)
        (algebraMap (ZMod AspisR1FoldInverses.Refinement.P) AspisWideTower.WideExact
          (R1ZCircleFoldMathV1.rustHalf * AspisR1FoldInverses.Refinement.decodeBase lx))
        (-(algebraMap (ZMod AspisR1FoldInverses.Refinement.P) AspisWideTower.WideExact
          (R1ZCircleFoldMathV1.rustHalf * AspisR1FoldInverses.Refinement.decodeBase ly)))
        (algebraMap (ZMod AspisR1FoldInverses.Refinement.P) AspisWideTower.WideExact
          (R1ZCircleFoldMathV1.rustHalf * AspisR1FoldInverses.Refinement.decodeBase lz))
        (AspisR1FoldInverses.Refinement.values4 (decodeFold a) (decodeFold b) (decodeFold c) (decodeFold d)) := by
  exact AspisR1FoldInverses.Refinement.line_model_success currentFoldOps CanonicalFold decodeFold
    current_operations_refine alpha a b c d out ix iy lx ly lz Ca Cb Cc Cd Calpha Clx Cly Clz h

#print axioms current_fold_scale
#print axioms current_operations_refine
#print axioms concrete_circle_model_success
#print axioms concrete_line_model_success
end AspisR1CurrentWide.Proof
