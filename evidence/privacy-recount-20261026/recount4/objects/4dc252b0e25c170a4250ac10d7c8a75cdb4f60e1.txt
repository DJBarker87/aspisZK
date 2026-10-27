import R1Z.ProverRwSuccessCtReduce
import R1Z.ProverCommitNativeOps47
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwSuccessNativeNormalizeWord
open Aeneas Aeneas.Std Result
abbrev source := ProverRwSuccessNativePorts.aspis_core.field.wide_exact.canonical_qm31.closure.Insts.CoreOpsFunctionFnTupleM31M31.call
abbrev cast64 (x : U32) : U64 := UScalar.cast .U64 x

theorem cast_value (x : U32) : (cast64 x).val=x.val := by scalar_tac

theorem word (x : U32) : source () x=.ok (ProverCommitNativeOps47.normalizeWord x) := by
  obtain ⟨z,hz,hv,_⟩ := AspisR1.ExtractedCurrentReducer.current_reduce_mod (cast64 x)
  have checked : AspisR1ProducerChecked47.field.reduce_u64 (cast64 x)=.ok z := by
    rw [ProverCommitPrimitive47.reduce,hz]
  have release := ProverCommitRelease47.reduce (cast64 x) z checked
  have value : z.val=x.val%2147483647 := by
    simpa only [cast_value,AspisCircleGroupOrder.P] using hv
  have same : z=ProverCommitNativeOps47.normalizeWord x := by
    apply UScalar.eq_of_val_eq
    rw [ProverCommitNativeOps47.normalize_val]
    exact value
  simp only [source,ProverRwSuccessNativePorts.aspis_core.field.wide_exact.canonical_qm31.closure.Insts.CoreOpsFunctionFnTupleM31M31.call,
    lift,bind_tc_ok,ProverRwSuccessCtReduce.reduce]
  change (do let z' ← AspisR1ProducerRelease47.field.reduce_u64 (cast64 x); .ok z') = _
  rw [release]
  simp only [bind_tc_ok,same,id_eq]
#print axioms cast_value
#print axioms word
end R1Z.ProverRwSuccessNativeNormalizeWord
