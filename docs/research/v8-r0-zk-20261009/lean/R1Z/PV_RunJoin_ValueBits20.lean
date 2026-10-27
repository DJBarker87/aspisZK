import R1Z.PV_RunJoin_CompilerChecks17
set_option autoImplicit false
namespace R1Z.PV_RunJoin_ValueBits20
open Aeneas Aeneas.Std Result
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1
open BuilderStdModels
abbrev closure := pair_trace.value_bits.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31

def bit (value : U32) (i : Usize) : U32 := U32.wrapping_shr value (UScalar.cast .U32 i) &&& 1#u32

def bits (value : U32) : Array U32 30#usize :=
  ⟨(indices 30#usize).map (bit value),by simp [indices]⟩

theorem call (value : U32) (i : Usize) : closure.call_mut value i = ok (bit value i,value) := rfl
#print axioms call

theorem loop (value : U32) (is : List Usize) :
    fromFnLoop closure is value = ok (is.map (bit value),value) := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    rw [fromFnLoop,call]
    simp only [bind_tc_ok]
    rw [ih]
    rfl
#print axioms loop

theorem source (value : U32) : pair_trace.value_bits value = ok (bits value) := by
  rw [pair_trace.value_bits]
  change fromFn 30#usize closure value = _
  rw [fromFn,loop]
  simp only [bind_tc_ok]
  rw [dif_pos (by simp [indices])]
  rfl
#print axioms source
end R1Z.PV_RunJoin_ValueBits20
