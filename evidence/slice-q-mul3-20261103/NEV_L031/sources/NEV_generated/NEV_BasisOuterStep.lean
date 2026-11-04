import NEV_BasisRaw
import NBF_BasisOuter
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace NEV_BasisOuterStep
open Aeneas Aeneas.Std Result ControlFlow AspisR1 AspisR1Stage2 Port3_NativeQueryBody

theorem multiply (x y : U32) : NEV_AccumulateRaw.aspis_core.field.M31.mul x y=
    AspisR1Qm31ArithmeticProbe.field.M31.mul x y := by
  rw [NEV_AccumulateRaw.aspis_core.field.M31.mul,NEI_FieldScalar.m_mul,
    AspisR1CurrentWide.Proof.m31_mul_same]
theorem subtract (x y : U32) : NEV_AccumulateRaw.aspis_core.field.M31.sub x y=
    AspisR1Qm31ArithmeticProbe.field.M31.sub x y := by
  rw [NEV_AccumulateRaw.aspis_core.field.M31.sub,NEI_FieldScalar.m_sub,
    AspisR1CurrentWide.Proof.m31_sub_same]
theorem double (x : U32) : NEV_AccumulateRaw.aspis_core.field.M31.double x=
    AspisR1Qm31ArithmeticProbe.field.M31.add x x := by
  change NEI_LineFull.aspis_core.field.M31.add x x=_
  rw [NEI_FieldScalar.m_add,AspisR1CurrentWide.Proof.m31_add_same]

/-- New emitted outer body uses the SAME retained inner loop, same node update,
and nonwrapping bounded doubling. No arithmetic recurrence is reproved. -/
theorem body (ops : Ops) (one node : U32) (width n : Usize)
    (basis : Array U32 256#usize) (small : n.val≤128) :
    NEV_AccumulateRaw.accumulate_batched_with_node_loop0.body one width node basis n =
      verifier.accumulate_batched_with_node_loop0.body
        (NBF_BasisInstall.install ops) one width node basis n := by
  have inner := NEV_BasisRaw.inner_loop ops node n n.val
    {start:=0#usize,«end»:=n} basis small rfl (by simp)
  have counter := NBF_BasisInstall.checked_mul n 2#usize (by change n.val*2≤4096;omega)
  simp [NEV_AccumulateRaw.accumulate_batched_with_node_loop0.body,
    verifier.accumulate_batched_with_node_loop0.body,inner,NBF_BasisInstall.install,
    multiply,subtract,double,counter,lift]

#print axioms multiply
#print axioms subtract
#print axioms double
#print axioms body
end NEV_BasisOuterStep
end
