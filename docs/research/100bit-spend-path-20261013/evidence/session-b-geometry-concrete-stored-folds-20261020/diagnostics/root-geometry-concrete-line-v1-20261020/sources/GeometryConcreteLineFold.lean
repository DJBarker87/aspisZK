import GeometryConcreteCircleFold
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1CurrentWide.Proof
open AspisR1GeometryInputs.Proof Aeneas.Std.alloc.vec
private abbrev LineCallback := AspisR1GeometryGrouping.geometry_groups.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut

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
    ∃ (u ix iy : AspisR1QueryGeometryActual.domain.FibreIndex)
      (hu : u.val<262144) (hix : ix.val<262144) (hiy : iy.val<262144),
      u.val=(queries.val.getD (start.val+i.val) 0#u32).val ∧
      ix.val=(u.val/4)*4 ∧ iy.val=(u.val/4)*4+3 ∧ CanonicalFold out ∧
      decodeFold out = AspisV5ComponentCConcreteFoldLinearity.lineFoldValue (decodeFold alpha)
        (algebraMap (ZMod AspisR1FoldInverses.Refinement.P) AspisWideTower.WideExact
          (R1ZCircleFoldMathV1.rustHalf *
            (AspisV7ExactOneFoldDomains.storedFirstLineX18 ⟨ix.val,hix⟩)⁻¹))
        (-(algebraMap (ZMod AspisR1FoldInverses.Refinement.P) AspisWideTower.WideExact
          (R1ZCircleFoldMathV1.rustHalf *
            (AspisV7ExactOneFoldDomains.storedFirstLineX18 ⟨iy.val,hiy⟩)⁻¹)))
        (algebraMap (ZMod AspisR1FoldInverses.Refinement.P) AspisWideTower.WideExact
          (R1ZCircleFoldMathV1.rustHalf *
            (2*(AspisV7ExactOneFoldDomains.storedFirstLineX18 ⟨ix.val,hix⟩)^2-1)⁻¹))
        (AspisR1FoldInverses.Refinement.values4 (decodeFold a) (decodeFold b) (decodeFold c) (decodeFold d)) := by
  obtain ⟨u,ix,iy,hu,hix,hiy,huq,hixv,hiyv,_,hvalx⟩ :=
    grouping_success_stored_inverse queries start end1 inverse zs hrun i 2#usize hi
      (by change (2:Nat)<5; decide) invlx capx hx
  obtain ⟨u1,ix1,iy1,hu1,hix1,hiy1,huq1,hixv1,hiyv1,_,hvaly⟩ :=
    grouping_success_stored_inverse queries start end1 inverse zs hrun i 3#usize hi
      (by change (3:Nat)<5; decide) invly capy hy
  obtain ⟨u2,ix2,iy2,hu2,hix2,hiy2,huq2,hixv2,hiyv2,_,hvalz⟩ :=
    grouping_success_stored_inverse queries start end1 inverse zs hrun i 4#usize hi
      (by change (4:Nat)<5; decide) invlz capz hz
  have he1 : u1=u := UScalar.eq_of_val_eq (huq1.trans huq.symm)
  subst u1
  have hey : iy1=iy := UScalar.eq_of_val_eq (hiyv1.trans hiyv.symm)
  subst iy1
  have he2 : u2=u := UScalar.eq_of_val_eq (huq2.trans huq.symm)
  subst u2
  have hex : ix2=ix := UScalar.eq_of_val_eq (hixv2.trans hixv.symm)
  subst ix2
  change AspisR1FoldInverses.Refinement.decodeBase invlx =
    (AspisV7ExactOneFoldDomains.storedFirstLineX18 ⟨ix.val,hix⟩)⁻¹ at hvalx
  change AspisR1FoldInverses.Refinement.decodeBase invly =
    (AspisV7ExactOneFoldDomains.storedFirstLineX18 ⟨iy.val,hiy⟩)⁻¹ at hvaly
  change AspisR1FoldInverses.Refinement.decodeBase invlz =
    (2*(AspisV7ExactOneFoldDomains.storedFirstLineX18 ⟨ix.val,hix⟩)^2-1)⁻¹ at hvalz
  have Cx : AspisR1FoldInverses.Refinement.CanonicalBase invlx :=
    grouping_success_canonical queries start end1 inverse zs hrun i 2#usize hi
      (by change (2:Nat)<5; decide) invlx capx hx
  have Cy : AspisR1FoldInverses.Refinement.CanonicalBase invly :=
    grouping_success_canonical queries start end1 inverse zs hrun i 3#usize hi
      (by change (3:Nat)<5; decide) invly capy hy
  have Cz : AspisR1FoldInverses.Refinement.CanonicalBase invlz :=
    grouping_success_canonical queries start end1 inverse zs hrun i 4#usize hi
      (by change (4:Nat)<5; decide) invlz capz hz
  obtain ⟨Cout,hout⟩ := concrete_line_model_success alpha a b c d out unusedx unusedy invlx invly invlz
    Ca Cb Cc Cd Calpha Cx Cy Cz hfold
  exact ⟨u,ix,iy,hu,hix,hiy,huq,hixv,hiyv,Cout,by simpa only [hvalx,hvaly,hvalz] using hout⟩

#print axioms geometry_line_fold_success
end AspisR1CurrentWide.Proof
