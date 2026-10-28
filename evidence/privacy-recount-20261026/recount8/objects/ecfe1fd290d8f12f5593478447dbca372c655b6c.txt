import R1Z.ProverRwSuccessCtSubtract
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwSuccessCtReduce
open Aeneas Aeneas.Std Result
abbrev source := ProverRwSuccessNativePorts.aspis_core.field.ct.reduce64
theorem reduce (x : U64) : source x=AspisR1ProducerRelease47.field.reduce_u64 x := by
  simp only [source,ProverRwSuccessNativePorts.aspis_core.field.ct.reduce64,
    ProverRwSuccessNativePorts.aspis_core.field.P,
    AspisR1ProducerRelease47.field.reduce_u64,lift,bind_tc_ok,
    ProverRwSuccessCtSubtract.subtract]
  split <;> rfl
#print axioms reduce
end R1Z.ProverRwSuccessCtReduce
