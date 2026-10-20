import GeometryStoredLineProjection
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1CurrentWide.Proof
open AspisR1GeometryInputs.Proof Aeneas.Std.alloc.vec

theorem geometry_stored_denominators_nonzero (queries : Array U32 22#usize)
    (start end1 i : Usize) (inverse zs : Vec U32)
    (hrun : geometryAndInvert concreteQueryValues queries start end1 = .ok (.Ok (inverse,zs)))
    (hi : i.val<end1.val-start.val)
    (g : StoredGeometryPoint (queries.val.getD (start.val+i.val) 0#u32)) :
    ∀ x ∈ storedDenominators g, x ≠ 0 := by
  obtain ⟨_,_,_,records,ht,_,_,hlen,_,_⟩ :=
    concrete_geometry_inverse_success queries start end1 inverse zs hrun
  have hri : i.val<records.length := by omega
  have hq := inputTrace_nth concreteQueryValues queries ht i.val hri
  have hr := concreteQueryValues_success_raw _ _ _ hq
  obtain ⟨u,ix,iy,hu,hix,hiy,huq,hixv,hiyv,hslots,_⟩ :=
    R17QueryValuesSlotsStored.emitted_success_slot_values _ R17SliceAnySourceV1.queryZeroAny _ _ hr
  let g1 : StoredGeometryPoint (queries.val.getD (start.val+i.val) 0#u32) :=
    ⟨u,ix,iy,hu,hix,hiy,huq,hixv,hiyv⟩
  have hslots1 : (records[i.val]).1.val.map R17CurrentM31Semantics.decode = storedDenominators g1 := hslots
  have he := congrArg (fun a => storedDenominators a) (stored_point_unique g1 g)
  have hslotsg := hslots1.trans he
  intro x hx
  rw [← hslotsg] at hx
  obtain ⟨raw,hraw,hx⟩ := List.mem_map.mp hx
  subst x
  exact concreteQueryValues_nonzero _ _ _ hq raw hraw

private theorem third_mem {A : Type} (a b c d e : A) : c ∈ [a,b,c,d,e] :=
  List.mem_cons_of_mem a (List.mem_cons_of_mem b (List.mem_cons_self c [d,e]))
private theorem fourth_mem {A : Type} (a b c d e : A) : d ∈ [a,b,c,d,e] :=
  List.mem_cons_of_mem a (List.mem_cons_of_mem b (List.mem_cons_of_mem c (List.mem_cons_self d [e])))
private theorem fifth_mem {A : Type} (a b c d e : A) : e ∈ [a,b,c,d,e] :=
  List.mem_cons_of_mem a (List.mem_cons_of_mem b (List.mem_cons_of_mem c (List.mem_cons_of_mem d (List.mem_cons_self e []))))

theorem geometry_stored_line_nonzero (queries : Array U32 22#usize)
    (start end1 i : Usize) (inverse zs : Vec U32)
    (hrun : geometryAndInvert concreteQueryValues queries start end1 = .ok (.Ok (inverse,zs)))
    (hi : i.val<end1.val-start.val)
    (g : StoredGeometryPoint (queries.val.getD (start.val+i.val) 0#u32)) :
    storedLineX g ≠ 0 ∧ storedLineY g ≠ 0 ∧ storedLineZ g ≠ 0 := by
  have hn := geometry_stored_denominators_nonzero queries start end1 i inverse zs hrun hi g
  exact ⟨hn _ (third_mem _ _ _ _ _),hn _ (fourth_mem _ _ _ _ _),hn _ (fifth_mem _ _ _ _ _)⟩
#print axioms geometry_stored_denominators_nonzero
#print axioms geometry_stored_line_nonzero
end AspisR1CurrentWide.Proof
