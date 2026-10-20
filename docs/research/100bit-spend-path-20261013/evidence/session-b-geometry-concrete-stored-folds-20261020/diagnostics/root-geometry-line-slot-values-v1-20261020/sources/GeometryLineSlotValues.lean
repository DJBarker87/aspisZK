import GeometryStoredPoint
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1CurrentWide.Proof
open AspisR1GeometryInputs.Proof Aeneas.Std.alloc.vec
private abbrev LineCallback := AspisR1GeometryGrouping.geometry_groups.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut
theorem geometry_line_slot_values (queries : Array U32 22#usize)
    (start end1 i : Usize) (inverse zs : Vec U32)
    (hrun : geometryAndInvert concreteQueryValues queries start end1 = .ok (.Ok (inverse,zs)))
    (hi : i.val<end1.val-start.val)
    (unusedx unusedy invlx invly invlz : U32)
    (capx capy capz : AspisR1GeometryGrouping.geometry_groups.closure.closure)
    (hx : LineCallback (inverse,i) 2#usize = .ok (invlx,capx))
    (hy : LineCallback (inverse,i) 3#usize = .ok (invly,capy))
    (hz : LineCallback (inverse,i) 4#usize = .ok (invlz,capz)) :
    ∃ g : StoredGeometryPoint (queries.val.getD (start.val+i.val) 0#u32),
      AspisR1FoldInverses.Refinement.CanonicalBase invlx ∧
      AspisR1FoldInverses.Refinement.CanonicalBase invly ∧
      AspisR1FoldInverses.Refinement.CanonicalBase invlz ∧
      AspisR1FoldInverses.Refinement.decodeBase invlx=(storedLineX g)⁻¹ ∧
      AspisR1FoldInverses.Refinement.decodeBase invly=(storedLineY g)⁻¹ ∧
      AspisR1FoldInverses.Refinement.decodeBase invlz=(storedLineZ g)⁻¹ := by
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
  exact ⟨g,Cx,Cy,Cz,hvalx,hvaly,hvalz⟩

#print axioms geometry_line_slot_values
end AspisR1CurrentWide.Proof
