import GeometryStoredPoint
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
  obtain ⟨g,Cx,hvalx⟩ := geometry_slot_inverse queries start end1 i 2#usize inverse zs hrun hi
    (by change (2:Nat)<5; decide) invlx capx hx
  obtain ⟨g1,Cy,hvaly⟩ := geometry_slot_inverse queries start end1 i 3#usize inverse zs hrun hi
    (by change (3:Nat)<5; decide) invly capy hy
  obtain ⟨g2,Cz,hvalz⟩ := geometry_slot_inverse queries start end1 i 4#usize inverse zs hrun hi
    (by change (4:Nat)<5; decide) invlz capz hz
  have he1 : g1=g := stored_point_unique g1 g
  have he2 : g2=g := stored_point_unique g2 g
  subst g1
  subst g2
  change AspisR1FoldInverses.Refinement.decodeBase invlx = (storedLineX g)⁻¹ at hvalx
  change AspisR1FoldInverses.Refinement.decodeBase invly = (storedLineY g)⁻¹ at hvaly
  change AspisR1FoldInverses.Refinement.decodeBase invlz = (storedLineZ g)⁻¹ at hvalz
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
