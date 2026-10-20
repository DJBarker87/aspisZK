import GeometryStoredParentLine
import GeometryConcreteLineFold
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1CurrentWide.Proof
open AspisR1GeometryInputs.Proof Aeneas.Std.alloc.vec
private abbrev LineCallback := AspisR1GeometryGrouping.geometry_groups.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut

theorem stored_line_fold_weights {q : U32} (g : StoredGeometryPoint q)
    (alpha : AspisWideTower.WideExact) (values : Fin 4 → AspisWideTower.WideExact) :
    AspisV5ComponentCConcreteFoldLinearity.lineFoldValue alpha
      (algebraMap (ZMod AspisR1FoldInverses.Refinement.P) AspisWideTower.WideExact
        (R1ZCircleFoldMathV1.rustHalf * (storedLineX g)⁻¹))
      (-(algebraMap (ZMod AspisR1FoldInverses.Refinement.P) AspisWideTower.WideExact
        (R1ZCircleFoldMathV1.rustHalf * (storedLineY g)⁻¹)))
      (algebraMap (ZMod AspisR1FoldInverses.Refinement.P) AspisWideTower.WideExact
        (R1ZCircleFoldMathV1.rustHalf * (storedLineZ g)⁻¹)) values =
    AspisV5ComponentCConcreteFoldLinearity.lineFoldValue alpha
      (algebraMap (ZMod AspisR1FoldInverses.Refinement.P) AspisWideTower.WideExact
        (R1ZQueryGeometryValuesV1.sourceLineInverse (storedParent g) 0))
      (algebraMap (ZMod AspisR1FoldInverses.Refinement.P) AspisWideTower.WideExact
        (R1ZQueryGeometryValuesV1.sourceLineInverse (storedParent g) 1))
      (algebraMap (ZMod AspisR1FoldInverses.Refinement.P) AspisWideTower.WideExact
        (R1ZQueryGeometryValuesV1.sourceLineInverse (storedParent g) 2)) values := by
  rw [stored_line_inverse_zero,stored_line_inverse_one,stored_line_inverse_two,map_neg]

theorem geometry_line_fold_parent_success (queries : Array U32 22#usize)
    (start end1 i : Usize) (inverse zs : Vec U32)
    (hrun : geometryAndInvert concreteQueryValues queries start end1 = .ok (.Ok (inverse,zs)))
    (hi : i.val<end1.val-start.val)
    (unusedx unusedy invlx invly invlz : U32)
    (capx capy capz : AspisR1GeometryGrouping.geometry_groups.closure.closure)
    (hx : LineCallback (inverse,i) 2#usize = .ok (invlx,capx))
    (hy : LineCallback (inverse,i) 3#usize = .ok (invly,capy))
    (hz : LineCallback (inverse,i) 4#usize = .ok (invlz,capz))
    (alpha a b c d out : FoldE)
    (Ca : CanonicalFold a) (Cb : CanonicalFold b) (Cc : CanonicalFold c)
    (Cd : CanonicalFold d) (Calpha : CanonicalFold alpha)
    (hfold : AspisR1FoldInverses.verifier.line_fold_with_inverses currentFoldOps alpha
      (Array.make 4#usize [a,b,c,d]) (Array.make 5#usize [unusedx,unusedy,invlx,invly,invlz]) = .ok out) :
    ∃ g : StoredGeometryPoint (queries.val.getD (start.val+i.val) 0#u32),
      CanonicalFold out ∧ storedLineX g ≠ 0 ∧ storedLineY g ≠ 0 ∧ storedLineZ g ≠ 0 ∧
      decodeFold out = AspisV5ComponentCConcreteFoldLinearity.lineFoldValue (decodeFold alpha)
        (algebraMap (ZMod AspisR1FoldInverses.Refinement.P) AspisWideTower.WideExact
          (R1ZQueryGeometryValuesV1.sourceLineInverse (storedParent g) 0))
        (algebraMap (ZMod AspisR1FoldInverses.Refinement.P) AspisWideTower.WideExact
          (R1ZQueryGeometryValuesV1.sourceLineInverse (storedParent g) 1))
        (algebraMap (ZMod AspisR1FoldInverses.Refinement.P) AspisWideTower.WideExact
          (R1ZQueryGeometryValuesV1.sourceLineInverse (storedParent g) 2))
        (AspisR1FoldInverses.Refinement.values4 (decodeFold a) (decodeFold b) (decodeFold c) (decodeFold d)) := by
  obtain ⟨g,Cout,hout⟩ := geometry_line_fold_success queries start end1 i inverse zs hrun hi
    unusedx unusedy invlx invly invlz capx capy capz hx hy hz alpha a b c d out
    Ca Cb Cc Cd Calpha hfold
  have hn := geometry_stored_line_nonzero queries start end1 i inverse zs hrun hi g
  exact ⟨g,Cout,hn.1,hn.2.1,hn.2.2,hout.trans (stored_line_fold_weights g _ _)⟩
#print axioms stored_line_fold_weights
#print axioms geometry_line_fold_parent_success
end AspisR1CurrentWide.Proof
