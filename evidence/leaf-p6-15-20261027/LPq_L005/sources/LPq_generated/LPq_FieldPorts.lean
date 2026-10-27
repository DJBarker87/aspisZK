import LPq_ScalarPorts
import XRy_ClaimArithmetic
set_option autoImplicit false
namespace AspisR1.LPq_FieldPorts
open Aeneas Aeneas.Std Result LPi_FieldValues XRo_Join_Carriers

def cm (x : NC) : XRn_Join_Release.aspis_core.field.CM31 := ⟨x.a,x.b⟩
def qm (x : NQ) : E.Q := ⟨cm x.c0,cm x.c1⟩
def wide (x : NE) : C.E :=
  ⟨XRn_Join_FieldExternal.oldQ (qm x.c0),XRn_Join_FieldExternal.oldQ (qm x.c1)⟩

theorem cm_add_graph (x y : NC) :
    mapR cm (FIo_Native.aspis_core.field.CM31.add x y)=
      XRn_Join_Field.field.CM31.add (cm x) (cm y) := by
  simp only [mapR,FIo_Native.aspis_core.field.CM31.add,
    XRn_Join_Field.field.CM31.add,cm,bind_assoc_eq,bind_tc_ok,LPq_ScalarPorts.add,LPq_ScalarPorts.sub,
    LPq_ScalarPorts.mul,LPq_ScalarPorts.wrapper,LPq_ScalarPorts.double]
  all_goals rfl

theorem cm_sub_graph (x y : NC) :
    mapR cm (FIo_Native.aspis_core.field.CM31.sub x y)=
      XRn_Join_Field.field.CM31.sub (cm x) (cm y) := by
  simp only [mapR,FIo_Native.aspis_core.field.CM31.sub,
    XRn_Join_Field.field.CM31.sub,cm,bind_assoc_eq,bind_tc_ok,LPq_ScalarPorts.add,LPq_ScalarPorts.sub,
    LPq_ScalarPorts.mul,LPq_ScalarPorts.wrapper,LPq_ScalarPorts.double]
  all_goals rfl

theorem cm_mul_graph (x y : NC) :
    mapR cm (FIo_Native.aspis_core.field.CM31.mul x y)=
      XRn_Join_Field.field.CM31.mul (cm x) (cm y) := by
  simp only [mapR,FIo_Native.aspis_core.field.CM31.mul,
    XRn_Join_Field.field.CM31.mul,cm,bind_assoc_eq,bind_tc_ok,LPq_ScalarPorts.add,LPq_ScalarPorts.sub,
    LPq_ScalarPorts.mul,LPq_ScalarPorts.wrapper,LPq_ScalarPorts.double]
  all_goals rfl

theorem by_r_graph (x : NC) :
    mapR cm (FIo_Native.aspis_core.field.mul_by_r x)=
      XRn_Join_Field.field.mul_by_r (cm x) := by
  simp only [mapR,FIo_Native.aspis_core.field.mul_by_r,
    XRn_Join_Field.field.mul_by_r,cm,bind_assoc_eq,bind_tc_ok,LPq_ScalarPorts.add,LPq_ScalarPorts.sub,
    LPq_ScalarPorts.mul,LPq_ScalarPorts.wrapper,LPq_ScalarPorts.double]
  all_goals rfl

theorem cm_add (x y : NC) (hx : canonC x) (hy : canonC y) :
    ∃ z, FIo_Native.aspis_core.field.CM31.add x y=ok z ∧ canonC z ∧
      XRn_Join_Field.field.CM31.add (cm x) (cm y)=ok (cm z) := by
  obtain ⟨z,hz,hc,_⟩ := LPi_FieldValues.cm_add x y hx hy
  exact ⟨z,hz,hc,by simpa only [mapR,hz,bind_tc_ok] using (cm_add_graph x y).symm⟩

theorem cm_sub (x y : NC) (hx : canonC x) (hy : canonC y) :
    ∃ z, FIo_Native.aspis_core.field.CM31.sub x y=ok z ∧ canonC z ∧
      XRn_Join_Field.field.CM31.sub (cm x) (cm y)=ok (cm z) := by
  obtain ⟨z,hz,hc,_⟩ := LPi_FieldValues.cm_sub x y hx hy
  exact ⟨z,hz,hc,by simpa only [mapR,hz,bind_tc_ok] using (cm_sub_graph x y).symm⟩

theorem cm_mul (x y : NC) (hx : canonC x) (hy : canonC y) :
    ∃ z, FIo_Native.aspis_core.field.CM31.mul x y=ok z ∧ canonC z ∧
      XRn_Join_Field.field.CM31.mul (cm x) (cm y)=ok (cm z) := by
  obtain ⟨z,hz,hc,_⟩ := LPi_FieldValues.cm_mul x y hx hy
  exact ⟨z,hz,hc,by simpa only [mapR,hz,bind_tc_ok] using (cm_mul_graph x y).symm⟩

theorem by_r (x : NC) (hx : canonC x) :
    ∃ z, FIo_Native.aspis_core.field.mul_by_r x=ok z ∧ canonC z ∧
      XRn_Join_Field.field.mul_by_r (cm x)=ok (cm z) := by
  obtain ⟨z,hz,hc,_⟩ := LPi_FieldValues.by_r x hx
  exact ⟨z,hz,hc,by simpa only [mapR,hz,bind_tc_ok] using (by_r_graph x).symm⟩

#print axioms cm_add_graph
#print axioms cm_sub_graph
#print axioms cm_mul_graph
#print axioms by_r_graph
#print axioms cm_add
#print axioms cm_sub
#print axioms cm_mul
#print axioms by_r
end AspisR1.LPq_FieldPorts
