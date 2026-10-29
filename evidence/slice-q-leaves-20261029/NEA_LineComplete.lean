import NEA_LineTail
import NEA_PointComplete
set_option autoImplicit false
namespace NEA_LineComplete
open Aeneas Aeneas.Std Result AspisR1QueryGeometryActual

theorem cohort (cm : CM31Ops) (physical : NEA_PointComplete.PhysicalInterpretation cm)
    (u : Usize) (admitted : NEA_PointBridge.PacketDomain u) :
    ∃ (p : domain.Point field.M31) (square out : U32),
      fast_domain.fibre_point cm u=ok p ∧
      p.x.val<2147483647 ∧ p.y.val<2147483647 ∧
      AspisR1Qm31ArithmeticProbe.field.M31.mul p.x p.x=ok square ∧
      square.val=(p.x.val*p.x.val)%2147483647 ∧
      NEA_Reference.line_double_sub_ref square=ok out ∧
      R17FibrePointLineNodeActual.line_node cm R17CurrentM31Semantics.operations u=ok out ∧
      out.val<2147483647 := by
  obtain ⟨a,b,z,canonical,_,_,point⟩ := NEA_PointComplete.cohort cm physical u admitted
  obtain ⟨square,product,value,cs⟩ := AspisR1.ExtractedCurrentReducer.current_mul_mod z.a z.a
  obtain ⟨d,add,_,cd⟩ := AspisR1.ExtractedCurrentM31AddSub.current_add_mod square square cs cs
  have doubled : AspisR1Qm31ArithmeticProbe.field.M31.double square=ok d := by
    simpa only [AspisR1Qm31ArithmeticProbe.field.M31.double] using add
  obtain ⟨out,sub,_,co⟩ := AspisR1.ExtractedCurrentM31AddSub.current_sub_mod d 1#u32 cd (by decide)
  have reference : NEA_Reference.line_double_sub_ref square=ok out := by
    rw [NEA_LineTail.reference square cs,doubled]
    simpa only [bind_tc_ok] using sub
  have line : R17FibrePointLineNodeActual.line_node cm R17CurrentM31Semantics.operations u=ok out := by
    simp only [R17FibrePointLineNodeActual.line_node,point,bind_tc_ok,
      R17CurrentM31Semantics.operations,product,doubled,sub]
  exact ⟨⟨z.a,z.b⟩,square,out,point,canonical.1,canonical.2,product,value,reference,line,co⟩

#print axioms cohort
#print axioms AspisR1.ExtractedCurrentReducer.current_mul_mod
end NEA_LineComplete
