import NEB_ActualGeometryPoint
set_option autoImplicit false
namespace NEB_GeometryDictionaryEq
open Aeneas Aeneas.Std Result AspisR1 AspisR1QueryGeometryActual

theorem point (u : Usize) :
    fast_domain.fibre_point R17CurrentCM31Semantics.operations u=
      fast_domain.fibre_point NEA_FieldProduct.ops u := by
  unfold fast_domain.fibre_point
  simp only [domain.FibreIndex.get,lift,bind_tc_ok]
  generalize readA : Array.index_usize fast_domain.TABLE_A (u &&& 511#usize)=ra
  cases ra with
  | fail e => rfl
  | div => rfl
  | ok a =>
    simp only [bind_tc_ok]
    rw [show fast_domain.table_value R17CurrentCM31Semantics.operations a=ok ⟨a.1,a.2⟩ from by cases a;rfl,
        show fast_domain.table_value NEA_FieldProduct.ops a=ok ⟨a.1,a.2⟩ from by cases a;rfl]
    simp only [bind_tc_ok]
    generalize shift : u >>> 9#i32=shifted
    cases shifted with
    | fail e => rfl
    | div => rfl
    | ok iB =>
      simp only [bind_tc_ok]
      generalize readB : Array.index_usize fast_domain.TABLE_B iB=rb
      cases rb with
      | fail e => rfl
      | div => rfl
      | ok b =>
        simp only [bind_tc_ok]
        rw [show fast_domain.table_value R17CurrentCM31Semantics.operations b=ok ⟨b.1,b.2⟩ from by cases b;rfl,
            show fast_domain.table_value NEA_FieldProduct.ops b=ok ⟨b.1,b.2⟩ from by cases b;rfl]
        simp only [bind_tc_ok]
        have ca := NEA_TableCanonical.readA (u &&& 511#usize)
          (NEB_PointSuccess.read_bound _ _ _ readA) a readA
        have cb := NEA_TableCanonical.readB iB (NEB_PointSuccess.read_bound _ _ _ readB) b readB
        rw [NEB_GeometryFieldPorts.cm_eq _ _ ca cb]

theorem line (u : Usize) :
    R17FibrePointLineNodeActual.line_node R17CurrentCM31Semantics.operations R17CurrentM31Semantics.operations u=
      R17FibrePointLineNodeActual.line_node NEA_FieldProduct.ops R17CurrentM31Semantics.operations u := by
  unfold R17FibrePointLineNodeActual.line_node
  rw [point]

theorem point_success (u : Usize) (p : domain.Point field.M31)
    (run : fast_domain.fibre_point R17CurrentCM31Semantics.operations u=ok p) :
    p.x.val<2147483647 ∧ p.y.val<2147483647 := by
  rw [point] at run
  exact NEB_PointSuccess.canonical u p run

theorem line_success (u : Usize) (out : U32)
    (run : R17FibrePointLineNodeActual.line_node R17CurrentCM31Semantics.operations
      R17CurrentM31Semantics.operations u=ok out) : out.val<2147483647 := by
  rw [line] at run
  exact NEB_LineCalls.successful u out run

#print axioms point
#print axioms line
#print axioms point_success
#print axioms line_success
end NEB_GeometryDictionaryEq
