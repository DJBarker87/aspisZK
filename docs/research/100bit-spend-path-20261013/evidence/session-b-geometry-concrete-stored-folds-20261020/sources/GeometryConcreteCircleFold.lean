import GeometryStoredInverse
import CurrentConcreteFolds
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1CurrentWide.Proof
open AspisR1GeometryInputs.Proof Aeneas.Std.alloc.vec

private abbrev Callback := AspisR1GeometryGrouping.geometry_groups.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut

theorem geometry_circle_fold_success (queries : Array U32 22#usize)
    (start end1 i : Usize) (inverse zs : Vec U32)
    (hrun : geometryAndInvert concreteQueryValues queries start end1 = .ok (.Ok (inverse,zs)))
    (hi : i.val<end1.val-start.val)
    (invx invy lx ly lz : U32)
    (capx capy : AspisR1GeometryGrouping.geometry_groups.closure.closure)
    (hx : Callback (inverse,i) 0#usize = .ok (invx,capx))
    (hy : Callback (inverse,i) 1#usize = .ok (invy,capy))
    (alpha a b c d out : FoldE)
    (Ca : CanonicalFold a) (Cb : CanonicalFold b) (Cc : CanonicalFold c)
    (Cd : CanonicalFold d) (Calpha : CanonicalFold alpha)
    (hfold : AspisR1FoldInverses.verifier.circle_fold_with_inverses currentFoldOps alpha
      (Array.make 4#usize [a,b,c,d]) (Array.make 5#usize [invx,invy,lx,ly,lz]) = .ok out) :
    ∃ (u : AspisR1QueryGeometryActual.domain.FibreIndex) (hu : u.val<262144),
      u.val=(queries.val.getD (start.val+i.val) 0#u32).val ∧ CanonicalFold out ∧
      decodeFold out = AspisV5ComponentCConcreteFoldLinearity.circleFoldValue (decodeFold alpha)
        (algebraMap (ZMod AspisR1FoldInverses.Refinement.P) AspisWideTower.WideExact
          (R1ZCircleFoldMathV1.rustHalf *
            (R17TableCirclePowerBridge.circleCoords
              (AspisV7ExactOneFoldDomains.storedInitialFibrePoint20 ⟨u.val,hu⟩)).re⁻¹))
        (algebraMap (ZMod AspisR1FoldInverses.Refinement.P) AspisWideTower.WideExact
          (R1ZCircleFoldMathV1.rustHalf *
            (R17TableCirclePowerBridge.circleCoords
              (AspisV7ExactOneFoldDomains.storedInitialFibrePoint20 ⟨u.val,hu⟩)).im⁻¹))
        (AspisR1FoldInverses.Refinement.values4 (decodeFold a) (decodeFold b) (decodeFold c) (decodeFold d)) := by
  obtain ⟨u,ix,iy,hu,hix,hiy,huq,_,_,_,hvalx⟩ :=
    grouping_success_stored_inverse queries start end1 inverse zs hrun i 0#usize hi
      (by change (0:Nat)<5; decide) invx capx hx
  obtain ⟨u1,ix1,iy1,hu1,hix1,hiy1,huq1,_,_,_,hvaly⟩ :=
    grouping_success_stored_inverse queries start end1 inverse zs hrun i 1#usize hi
      (by change (1:Nat)<5; decide) invy capy hy
  have he : u1=u := UScalar.eq_of_val_eq (huq1.trans huq.symm)
  subst u1
  change AspisR1FoldInverses.Refinement.decodeBase invx = _ at hvalx
  change AspisR1FoldInverses.Refinement.decodeBase invy = _ at hvaly
  change AspisR1FoldInverses.Refinement.decodeBase invx =
    (R17TableCirclePowerBridge.circleCoords
      (AspisV7ExactOneFoldDomains.storedInitialFibrePoint20 ⟨u.val,hu⟩)).re⁻¹ at hvalx
  change AspisR1FoldInverses.Refinement.decodeBase invy =
    (R17TableCirclePowerBridge.circleCoords
      (AspisV7ExactOneFoldDomains.storedInitialFibrePoint20 ⟨u.val,hu⟩)).im⁻¹ at hvaly
  have Cx : AspisR1FoldInverses.Refinement.CanonicalBase invx :=
    grouping_success_canonical queries start end1 inverse zs hrun i 0#usize hi
      (by change (0:Nat)<5; decide) invx capx hx
  have Cy : AspisR1FoldInverses.Refinement.CanonicalBase invy :=
    grouping_success_canonical queries start end1 inverse zs hrun i 1#usize hi
      (by change (1:Nat)<5; decide) invy capy hy
  obtain ⟨Cout,hout⟩ := concrete_circle_model_success alpha a b c d out invx invy lx ly lz
    Ca Cb Cc Cd Calpha Cx Cy hfold
  exact ⟨u,hu,huq,Cout,by simpa only [hvalx,hvaly] using hout⟩

#print axioms geometry_circle_fold_success
end AspisR1CurrentWide.Proof
