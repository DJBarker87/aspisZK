import GeometryConcreteCircleFold
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1CurrentWide.Proof
open AspisR1GeometryInputs.Proof Aeneas.Std.alloc.vec
private abbrev LineCallback := AspisR1GeometryGrouping.geometry_groups.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut

structure StoredGeometryPoint (q : U32) where
  u : AspisR1QueryGeometryActual.domain.FibreIndex
  ix : AspisR1QueryGeometryActual.domain.FibreIndex
  iy : AspisR1QueryGeometryActual.domain.FibreIndex
  hu : u.val<262144
  hix : ix.val<262144
  hiy : iy.val<262144
  queryIndex : u.val=q.val
  ixIndex : ix.val=(u.val/4)*4
  iyIndex : iy.val=(u.val/4)*4+3

theorem stored_point_unique {q : U32} (a b : StoredGeometryPoint q) : a=b := by
  have h0 : a.u=b.u := UScalar.eq_of_val_eq (a.queryIndex.trans b.queryIndex.symm)
  have h1 : a.ix=b.ix := UScalar.eq_of_val_eq (by rw [a.ixIndex,b.ixIndex,h0])
  have h2 : a.iy=b.iy := UScalar.eq_of_val_eq (by rw [a.iyIndex,b.iyIndex,h0])
  cases a; cases b; cases h0; cases h1; cases h2; rfl

def storedLineX {q : U32} (g : StoredGeometryPoint q) : ZMod AspisR1FoldInverses.Refinement.P :=
  AspisV7ExactOneFoldDomains.storedFirstLineX18 ⟨g.ix.val,g.hix⟩
def storedLineY {q : U32} (g : StoredGeometryPoint q) : ZMod AspisR1FoldInverses.Refinement.P :=
  AspisV7ExactOneFoldDomains.storedFirstLineX18 ⟨g.iy.val,g.hiy⟩
def storedLineZ {q : U32} (g : StoredGeometryPoint q) : ZMod AspisR1FoldInverses.Refinement.P :=
  2*storedLineX g^2-1
def storedDenominators {q : U32} (g : StoredGeometryPoint q) : List (ZMod AspisR1FoldInverses.Refinement.P) :=
  [(R17TableCirclePowerBridge.circleCoords
     (AspisV7ExactOneFoldDomains.storedInitialFibrePoint20 ⟨g.u.val,g.hu⟩)).re,
   (R17TableCirclePowerBridge.circleCoords
     (AspisV7ExactOneFoldDomains.storedInitialFibrePoint20 ⟨g.u.val,g.hu⟩)).im,
   storedLineX g,storedLineY g,storedLineZ g]

theorem geometry_slot_inverse (queries : Array U32 22#usize)
    (start end1 i j : Usize) (inverse zs : Vec U32)
    (hrun : geometryAndInvert concreteQueryValues queries start end1 = .ok (.Ok (inverse,zs)))
    (hi : i.val<end1.val-start.val) (hj : j.val<5)
    (x : U32) (capture : AspisR1GeometryGrouping.geometry_groups.closure.closure)
    (hc : LineCallback (inverse,i) j = .ok (x,capture)) :
    ∃ g : StoredGeometryPoint (queries.val.getD (start.val+i.val) 0#u32),
      AspisR1FoldInverses.Refinement.CanonicalBase x ∧
      AspisR1FoldInverses.Refinement.decodeBase x = ((storedDenominators g).getD j.val 0)⁻¹ := by
  obtain ⟨u,ix,iy,hu,hix,hiy,huq,hixv,hiyv,_,hval⟩ :=
    grouping_success_stored_inverse queries start end1 inverse zs hrun i j hi hj x capture hc
  have hx := grouping_success_canonical queries start end1 inverse zs hrun i j hi hj x capture hc
  exact ⟨⟨u,ix,iy,hu,hix,hiy,huq,hixv,hiyv⟩,hx,hval⟩

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

#print axioms stored_point_unique
#print axioms geometry_slot_inverse
#print axioms geometry_line_fold_success
end AspisR1CurrentWide.Proof
