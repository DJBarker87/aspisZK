import NEB_TableCalls
import NEB_LineCalls
import NBG_InverseBridge
set_option autoImplicit false
namespace NEB_GeometryFieldPorts
open Aeneas Aeneas.Std Result AspisR1 AspisR1QueryGeometryActual LPi_FieldValues

theorem add (x y : U32) (hx : x.val<2147483647) (hy : y.val<2147483647) :
    FIo_Native.aspis_core.field.M31.add x y=AspisR1Qm31ArithmeticProbe.field.M31.add x y := by
  obtain ⟨a,ha,va,_⟩ := LPi_NatBase.add x y hx hy
  obtain ⟨b,hb,vb,_⟩ := ExtractedCurrentM31AddSub.current_add_mod x y hx hy
  have same : a=b := UScalar.eq_of_val_eq (va.trans vb.symm)
  rw [ha,hb,same]

theorem sub (x y : U32) (hx : x.val<2147483647) (hy : y.val<2147483647) :
    FIo_Native.aspis_core.field.M31.sub x y=AspisR1Qm31ArithmeticProbe.field.M31.sub x y := by
  obtain ⟨a,ha,va,_⟩ := LPi_NatBase.sub x y hx hy
  obtain ⟨b,hb,vb,_⟩ := ExtractedCurrentM31AddSub.current_sub_mod x y hx hy
  have same : a=b := UScalar.eq_of_val_eq (va.trans vb.symm)
  rw [ha,hb,same]

theorem double (x : U32) (hx : x.val<2147483647) :
    FIo_Native.aspis_core.field.M31.double x=AspisR1Qm31ArithmeticProbe.field.M31.double x := by
  exact add x x hx hx

/-- Instantiate the ACTUAL adopted geometry dictionary, not only a new emitted
field dictionary with similar field names. -/
theorem physical : NEA_PointComplete.PhysicalInterpretation R17CurrentCM31Semantics.operations := by
  refine ⟨fun _ _ => rfl,?_⟩
  intro x y hx hy
  obtain ⟨z,run,cz,real,imag⟩ := ExtractedCurrentCM31Mul.current_mul_words
    (R17CurrentCM31Semantics.toArithmetic x) (R17CurrentCM31Semantics.toArithmetic y) hx hy
  refine ⟨R17CurrentCM31Semantics.fromArithmetic z,?_,cz,?_⟩
  · simp only [R17CurrentCM31Semantics.operations,run,bind_tc_ok]
  · apply Prod.ext
    · simpa only [R17CurrentCM31Semantics.fromArithmetic,R17CurrentCM31Semantics.toArithmetic,
        LPi_FieldValues.mulC,LPi_CMProduct.realWord,ExtractedCurrentCM31Mul.realWord] using real
    · simpa only [R17CurrentCM31Semantics.fromArithmetic,R17CurrentCM31Semantics.toArithmetic,
        LPi_FieldValues.mulC,LPi_CMProduct.imagWord,ExtractedCurrentCM31Mul.imagWord] using imag

theorem cm_eq (x y : field.CM31) (hx : NEA_FieldProduct.Canonical x) (hy : NEA_FieldProduct.Canonical y) :
    R17CurrentCM31Semantics.operations.mul x y=NEA_FieldProduct.ops.mul x y := by
  obtain ⟨a,ha,_,va⟩ := physical.multiply x y hx hy
  obtain ⟨b,hb,_,vb⟩ := NEA_PointComplete.emitted_interpretation.multiply x y hx hy
  have values : (a.a.val,a.b.val)=(b.a.val,b.b.val) := va.trans vb.symm
  have ae : a.a=b.a := UScalar.eq_of_val_eq (congrArg Prod.fst values)
  have be : a.b=b.b := UScalar.eq_of_val_eq (congrArg Prod.snd values)
  have same : a=b := by cases a;cases b;simp_all
  rw [ha,hb,same]

#print axioms add
#print axioms sub
#print axioms double
#print axioms physical
#print axioms cm_eq
#print axioms NBG_InverseBridge.mul_eq_probe
end NEB_GeometryFieldPorts
