import Port5Q1_Domain
import R17CurrentDomainCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAQ_Geometry
open Aeneas Aeneas.Std Result
abbrev Point := AspisR1Stage2.aspis_core.r0.domain.Point U32

def point (u : Usize) : Result Point := do
  let p ← AspisR1QueryGeometryActual.fast_domain.fibre_point R17CurrentCM31Semantics.operations u
  ok ⟨p.x,p.y⟩

def line (u : Usize) : Result U32 :=
  R17FibrePointLineNodeActual.line_node
    R17CurrentCM31Semantics.operations R17CurrentM31Semantics.operations u

def install {C : Type} (ops : Port3_NativeGeometryBody.Ops C) :
    Port3_NativeGeometryBody.Ops C :=
  {ops with op7 := ok 1#u32
            op8 := AspisR1Qm31ArithmeticProbe.field.M31.sub
            op9 := AspisR1Qm31ArithmeticProbe.field.M31.mul
            op10 := AspisR1Qm31ArithmeticProbe.field.M31.double
            op14 := line
            op15 := point}

theorem canonical {C : Type} (ops : Port3_NativeGeometryBody.Ops C) :
    Port5Q1_GeometryCanonical.SessionAPrimitives (install ops) := by
  constructor
  · intro u p run
    obtain ⟨out,ho,he⟩ := Port3_PushFrame.bind_success _ _ _ run
    have same : (⟨out.x,out.y⟩ : Point)=p := Result.ok.inj he
    subst p
    exact R17CurrentDomainCanonical.fibre_point_success_canonical u out ho
  · intro u x run
    exact R17CurrentDomainCanonical.line_node_success_canonical u x run
  · intro x y z _ _ run
    exact R17CurrentDomainCanonical.mul_success_canonical x y z run
  · intro x y hx run
    exact R17CurrentDomainCanonical.double_success_canonical x y hx run
  · intro x run
    have same : 1#u32=x := Result.ok.inj run
    subst x
    change (1:Nat)<2147483647
    decide
  · intro x y z hx hy run
    exact R17CurrentDomainCanonical.sub_success_canonical x y z hx hy run

theorem multiply {C : Type} (ops : Port3_NativeGeometryBody.Ops C) :
    (install ops).op9=AspisR1Qm31ArithmeticProbe.field.M31.mul := rfl

theorem one {C : Type} (ops : Port3_NativeGeometryBody.Ops C) :
    (install ops).op7=ok 1#u32 := rfl

#print axioms canonical
#print axioms multiply
#print axioms one
#print AspisR1QueryGeometryActual.fast_domain.fibre_point
#print Aeneas.Std.Array.index_usize
end AspisR1.SAQ_Geometry
end
