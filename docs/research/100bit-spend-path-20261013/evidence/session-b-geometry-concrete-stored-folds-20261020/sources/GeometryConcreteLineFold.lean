import GeometryLineSlotValues
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1CurrentWide.Proof
open AspisR1GeometryInputs.Proof Aeneas.Std.alloc.vec
private abbrev LineCallback := AspisR1GeometryGrouping.geometry_groups.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut
private theorem apply_three {A B C D : Type} (f : A → B → C → D)
    {a a1 : A} {b b1 : B} {c c1 : C} (ha : a=a1) (hb : b=b1) (hc : c=c1) :
    f a b c=f a1 b1 c1 := by
  cases ha; cases hb; cases hc; rfl

theorem geometry_line_fold_success (queries : Array U32 22#usize)
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
      CanonicalFold out ∧
      decodeFold out = AspisV5ComponentCConcreteFoldLinearity.lineFoldValue (decodeFold alpha)
        (algebraMap (ZMod AspisR1FoldInverses.Refinement.P) AspisWideTower.WideExact
          (R1ZCircleFoldMathV1.rustHalf * (storedLineX g)⁻¹))
        (-(algebraMap (ZMod AspisR1FoldInverses.Refinement.P) AspisWideTower.WideExact
          (R1ZCircleFoldMathV1.rustHalf * (storedLineY g)⁻¹)))
        (algebraMap (ZMod AspisR1FoldInverses.Refinement.P) AspisWideTower.WideExact
          (R1ZCircleFoldMathV1.rustHalf * (storedLineZ g)⁻¹))
        (AspisR1FoldInverses.Refinement.values4 (decodeFold a) (decodeFold b) (decodeFold c) (decodeFold d)) := by
  obtain ⟨g,Cx,Cy,Cz,hvalx,hvaly,hvalz⟩ := geometry_line_slot_values queries start end1 i inverse zs
    hrun hi unusedx unusedy invlx invly invlz capx capy capz hx hy hz
  obtain ⟨Cout,hout⟩ := concrete_line_model_success alpha a b c d out unusedx unusedy invlx invly invlz
    Ca Cb Cc Cd Calpha Cx Cy Cz hfold
  have hmodel := apply_three (fun x y z : ZMod AspisR1FoldInverses.Refinement.P =>
    AspisV5ComponentCConcreteFoldLinearity.lineFoldValue (decodeFold alpha)
      (algebraMap (ZMod AspisR1FoldInverses.Refinement.P) AspisWideTower.WideExact
        (R1ZCircleFoldMathV1.rustHalf*x))
      (-(algebraMap (ZMod AspisR1FoldInverses.Refinement.P) AspisWideTower.WideExact
        (R1ZCircleFoldMathV1.rustHalf*y)))
      (algebraMap (ZMod AspisR1FoldInverses.Refinement.P) AspisWideTower.WideExact
        (R1ZCircleFoldMathV1.rustHalf*z))
      (AspisR1FoldInverses.Refinement.values4 (decodeFold a) (decodeFold b) (decodeFold c) (decodeFold d)))
    hvalx hvaly hvalz
  exact ⟨g,Cout,hout.trans hmodel⟩

#print axioms geometry_line_fold_success
end AspisR1CurrentWide.Proof
