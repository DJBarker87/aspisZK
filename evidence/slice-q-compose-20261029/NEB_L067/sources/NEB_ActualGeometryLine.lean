import NEB_GeometryDictionaryEq
set_option autoImplicit false
namespace NEB_ActualGeometryLine
open Aeneas Aeneas.Std Result AspisR1 AspisR1QueryGeometryActual

theorem calls {S Event : Type} (state : S) (u : Usize) (admitted : NEA_PointBridge.PacketDomain u) :
    ∃ (point : domain.Point field.M31) (square doubled out : U32),
      fast_domain.fibre_point R17CurrentCM31Semantics.operations u=ok point ∧
      point.x.val<2147483647 ∧ point.y.val<2147483647 ∧
      FIo_Native.aspis_core.field.M31.mul point.x point.x=ok square ∧ square.val<2147483647 ∧
      FIo_Native.aspis_core.field.M31.double square=ok doubled ∧ doubled.val<2147483647 ∧
      FIo_Native.aspis_core.field.M31.sub doubled 1#u32=ok out ∧ out.val<2147483647 ∧
      NEA_Reference.line_double_sub_ref square=ok out ∧
      R17FibrePointLineNodeActual.line_node R17CurrentCM31Semantics.operations
        R17CurrentM31Semantics.operations u=ok out ∧
      NEB_PureFrame.run (Event:=Event) state
        (R17FibrePointLineNodeActual.line_node R17CurrentCM31Semantics.operations
          R17CurrentM31Semantics.operations u)=ok (out,state,[]) := by
  obtain ⟨p,square,out,point,cx,cy,product,value,reference,line,co⟩ :=
    NEA_LineComplete.cohort R17CurrentCM31Semantics.operations NEB_GeometryFieldPorts.physical u admitted
  obtain ⟨s,run,_,cs⟩ := ExtractedCurrentReducer.current_mul_mod p.x p.x
  have same : s=square := Result.ok.inj (run.symm.trans product)
  subst s
  have nativeProduct : FIo_Native.aspis_core.field.M31.mul p.x p.x=ok square :=
    (NBG_InverseBridge.mul_eq_probe _ _).trans product
  obtain ⟨d,add,_,cd⟩ := ExtractedCurrentM31AddSub.current_add_mod square square cs cs
  have probeDouble : AspisR1Qm31ArithmeticProbe.field.M31.double square=ok d := by
    simpa only [AspisR1Qm31ArithmeticProbe.field.M31.double] using add
  have nativeDouble : FIo_Native.aspis_core.field.M31.double square=ok d :=
    (NEB_GeometryFieldPorts.double square cs).trans probeDouble
  have probeSub : AspisR1Qm31ArithmeticProbe.field.M31.sub d 1#u32=ok out := by
    rw [NEA_LineTail.reference square cs,probeDouble] at reference
    simpa only [bind_tc_ok] using reference
  have nativeSub : FIo_Native.aspis_core.field.M31.sub d 1#u32=ok out :=
    (NEB_GeometryFieldPorts.sub d 1#u32 cd (by decide)).trans probeSub
  exact ⟨p,square,d,out,point,cx,cy,nativeProduct,cs,nativeDouble,cd,nativeSub,co,
    reference,line,NEB_PureFrame.successful state _ _ line⟩

#print axioms calls
end NEB_ActualGeometryLine
