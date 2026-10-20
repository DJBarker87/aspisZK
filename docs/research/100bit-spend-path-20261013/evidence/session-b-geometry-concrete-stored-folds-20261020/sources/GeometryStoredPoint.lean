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


#print axioms stored_point_unique
#print axioms geometry_slot_inverse
end AspisR1CurrentWide.Proof
