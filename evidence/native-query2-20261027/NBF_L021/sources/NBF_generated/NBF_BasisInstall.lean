import NBF_Basis
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace NBF_BasisInstall
open AspisR1 AspisR1Stage2 Port3_NativeQueryBody
/-- Scalar arithmetic uses the retained emitted probe definitions. Connecting
these callbacks to native field calls is the named NBC_FieldOps dependency. -/
def install (ops : Ops) : Ops :=
 {ops with op4:=ok 0#u32,op5:=ok 1#u32,
   op6:=AspisR1Qm31ArithmeticProbe.field.M31.sub,
   op7:=AspisR1Qm31ArithmeticProbe.field.M31.mul,
   op8:=fun x=>AspisR1Qm31ArithmeticProbe.field.M31.add x x}

theorem block (ops : Ops) (basis : Array U32 256#usize) (node : U32)
 (n : Usize) (hn : n.val≤128) :
 verifier.accumulate_batched_with_node_loop0_loop0 (install ops)
   {start:=0#usize,«end»:=n} node basis n=
 S7Kani2BasisLoop.basis_block_owned AspisR1Qm31ArithmeticProbe.field.M31.mul
   basis node n 0#usize := by
 rw [NBF_Basis.iterate (install ops) node n n.val
   {start:=0#usize,«end»:=n} basis hn rfl (by simp)]
 rw [S7Kani2BasisLoop.extracted_basis_block_composition _ basis node n 0#usize n.val hn (by simp)]
 rfl

theorem checked_mul (x y : Usize) (small : x.val*y.val≤4096) :
 (x*y : Result Usize)=ok (Usize.wrapping_mul x y) := by
 have capacity : 4096≤Usize.max := by scalar_tac
 have spec : WP.spec (x*y : Result Usize) (fun out=>out.val=x.val*y.val) := by
   apply UScalar.mul_spec
   simpa only [UScalar.max_USize_eq] using small.trans capacity
 obtain ⟨out,run,value⟩ := WP.spec_imp_exists spec
 have same : out=Usize.wrapping_mul x y := by
   apply UScalar.eq_of_val_eq
   exact value.trans (Port3_Wrapping.wrap_mul_value x y small).symm
 exact run.trans (congrArg Result.ok same)
#print axioms block
#print axioms checked_mul
end NBF_BasisInstall
