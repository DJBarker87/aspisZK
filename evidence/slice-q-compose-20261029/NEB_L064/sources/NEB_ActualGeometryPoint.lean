import NEB_GeometryFieldPorts
set_option autoImplicit false
namespace NEB_ActualGeometryPoint
open Aeneas Aeneas.Std Result AspisR1 AspisR1QueryGeometryActual

/-- The actual selected table reads establish both product domains; the
original deployed-cohort dictionary is used in the returned point equation. -/
theorem calls (u : Usize) (admitted : NEA_PointBridge.PacketDomain u) :
    ∃ (iA iB : Usize) (a b : U32 × U32) (z : field.CM31),
      lift (u &&& 511#usize)=ok iA ∧ u >>> 9#i32=ok iB ∧
      Array.index_usize fast_domain.TABLE_A iA=ok a ∧
      Array.index_usize fast_domain.TABLE_B iB=ok b ∧
      NEA_FieldProduct.Canonical ⟨a.1,a.2⟩ ∧ NEA_FieldProduct.Canonical ⟨b.1,b.2⟩ ∧
      NEA_FieldProduct.ops.mul ⟨a.1,a.2⟩ ⟨b.1,b.2⟩=ok z ∧
      R17CurrentCM31Semantics.operations.mul ⟨a.1,a.2⟩ ⟨b.1,b.2⟩=ok z ∧
      NEA_FieldProduct.Canonical z ∧
      NEA_PointParam.point_ref u fast_domain.TABLE_A fast_domain.TABLE_B
        (Array.make 2#usize [z.a,z.b])=ok (NEA_PointBridge.record a b z) ∧
      fast_domain.fibre_point R17CurrentCM31Semantics.operations u=ok ⟨z.a,z.b⟩ := by
  obtain ⟨iA,iB,a,b,z,mask,shift,readA,readB,ca,cb,mul,cz,_⟩ :=
    NEB_PointCalls.selected_product u admitted
  have actual : R17CurrentCM31Semantics.operations.mul ⟨a.1,a.2⟩ ⟨b.1,b.2⟩=ok z :=
    (NEB_GeometryFieldPorts.cm_eq _ _ ca cb).trans mul
  have selected := NEA_PointBridge.selected R17CurrentCM31Semantics.operations u iA iB a b z
    mask shift readA readB (fun _ _ => rfl) actual
  exact ⟨iA,iB,a,b,z,mask,shift,readA,readB,ca,cb,mul,actual,cz,selected.1,selected.2⟩

theorem frame {S Event : Type} (state : S) (u : Usize) (admitted : NEA_PointBridge.PacketDomain u) :
    ∃ point : domain.Point field.M31,
      fast_domain.fibre_point R17CurrentCM31Semantics.operations u=ok point ∧
      point.x.val<2147483647 ∧ point.y.val<2147483647 ∧
      NEB_PureFrame.run (Event:=Event) state
        (fast_domain.fibre_point R17CurrentCM31Semantics.operations u)=ok (point,state,[]) := by
  obtain ⟨_,_,_,_,z,_,_,_,_,_,_,_,_,cz,_,run⟩ := calls u admitted
  exact ⟨⟨z.a,z.b⟩,run,cz.1,cz.2,NEB_PureFrame.successful state _ _ run⟩

#print axioms calls
#print axioms frame
end NEB_ActualGeometryPoint
