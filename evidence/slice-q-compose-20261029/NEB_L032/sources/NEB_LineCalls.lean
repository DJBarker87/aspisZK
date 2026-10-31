import NEB_PointSuccess
import NEA_LineComplete
set_option autoImplicit false
namespace NEB_LineCalls
open Aeneas Aeneas.Std Result AspisR1QueryGeometryActual
open AspisR1.Port3_PushFrame (bind_success)

/-- Every inner point/field domain is discharged by the SAME emitted path. -/
theorem admitted (u : Usize) (domain : NEA_PointBridge.PacketDomain u) :
    ∃ (point : AspisR1QueryGeometryActual.domain.Point field.M31) (square out : U32),
      fast_domain.fibre_point NEA_FieldProduct.ops u=ok point ∧
      point.x.val<2147483647 ∧ point.y.val<2147483647 ∧
      AspisR1Qm31ArithmeticProbe.field.M31.mul point.x point.x=ok square ∧
      square.val<2147483647 ∧
      NEA_Reference.line_double_sub_ref square=ok out ∧
      R17FibrePointLineNodeActual.line_node NEA_FieldProduct.ops R17CurrentM31Semantics.operations u=ok out ∧
      out.val<2147483647 := by
  obtain ⟨p,square,out,point,cx,cy,product,value,reference,line,co⟩ :=
    NEA_LineComplete.cohort NEA_FieldProduct.ops NEA_PointComplete.emitted_interpretation u domain
  obtain ⟨s,run,_,cs⟩ := AspisR1.ExtractedCurrentReducer.current_mul_mod p.x p.x
  have same : s=square := Result.ok.inj (run.symm.trans product)
  exact ⟨p,square,out,point,cx,cy,product,same ▸ cs,reference,line,co⟩

/-- Even an unrestricted alias index can produce only canonical line output
on success; no second point-success or field-domain premise is introduced. -/
theorem successful (u : Usize) (out : U32)
    (run : R17FibrePointLineNodeActual.line_node NEA_FieldProduct.ops
      R17CurrentM31Semantics.operations u=ok out) : out.val<2147483647 := by
  unfold R17FibrePointLineNodeActual.line_node at run
  obtain ⟨p,point,run⟩ := bind_success _ _ _ run
  have cp := NEB_PointSuccess.canonical u p point
  obtain ⟨square,mul,run⟩ := bind_success _ _ _ run
  obtain ⟨d,doubled,run⟩ := bind_success _ _ _ run
  obtain ⟨s,product,_,cs⟩ := AspisR1.ExtractedCurrentReducer.current_mul_mod p.x p.x
  have sameSquare : square=s := Result.ok.inj (mul.symm.trans product)
  subst square
  obtain ⟨double,add,_,cd⟩ := AspisR1.ExtractedCurrentM31AddSub.current_add_mod s s cs cs
  have doubleRun : AspisR1Qm31ArithmeticProbe.field.M31.double s=ok double := by
    simpa only [AspisR1Qm31ArithmeticProbe.field.M31.double] using add
  have sameDouble : d=double := Result.ok.inj (doubled.symm.trans doubleRun)
  subst d
  obtain ⟨z,sub,_,cz⟩ := AspisR1.ExtractedCurrentM31AddSub.current_sub_mod double 1#u32 cd (by decide)
  have sameOut : out=z := Result.ok.inj (run.symm.trans sub)
  exact sameOut.symm ▸ cz

#print axioms admitted
#print axioms successful
end NEB_LineCalls
