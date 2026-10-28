import NDO_JFs_TX2_PointCall
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFv_TX2_LineCall
open Aeneas Aeneas.Std Result
open AspisR1QueryGeometryActual

theorem source (u : Usize) (point : domain.Point U32)
    (hp : fast_domain.fibre_point R17CurrentCM31Semantics.operations u=ok point) :
    ∃ z, R17FibrePointLineNodeActual.line_node R17CurrentCM31Semantics.operations
      R17CurrentM31Semantics.operations u=ok z ∧ z.val<2147483647 ∧
      z.val=(((point.x.val*point.x.val)%2147483647+(point.x.val*point.x.val)%2147483647)%2147483647+2147483647-1)%2147483647 := by
  obtain ⟨square,hs,vs,cs⟩ := ExtractedCurrentReducer.current_mul_mod point.x point.x
  obtain ⟨doubled,hd,vd,cd⟩ := ExtractedCurrentM31AddSub.current_add_mod square square cs cs
  obtain ⟨z,hz,vz,cz⟩ := ExtractedCurrentM31AddSub.current_sub_mod doubled 1#u32 cd (by decide)
  refine ⟨z,?_,cz,?_⟩
  · simp only [R17FibrePointLineNodeActual.line_node,hp,R17CurrentM31Semantics.operations,
      AspisR1Qm31ArithmeticProbe.field.M31.double,hs,hd,hz,bind_tc_ok]
  · simpa only [vs,vd,show (1#u32).val=1 from rfl] using vz

#print axioms source
end AspisR1.JFv_TX2_LineCall
end
