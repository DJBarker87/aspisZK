import JGx_SdkEncoded
import JGx_SdkConstants
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGx_SdkLength
open Aeneas Aeneas.Std Result
open _root_.AdapterRw

theorem source (ops : Ops) (validated : r1_pool_adapter.ValidatedAsqa)
    (rawProof checkpoint : Slice U8) (encoded : Array U8 1880#usize)
    (proofLength : validated.proof_length=57607#usize) (rawLength : Slice.len rawProof=58295#usize)
    (encoder : ops.op22 validated.statement=ok (.Ok encoded)) :
    JGx_SdkCheckpointRead.afterCheckpoint ops validated rawProof checkpoint=
      JGx_SdkEncoded.afterEncoded ops validated rawProof checkpoint encoded := by
  unfold JGx_SdkCheckpointRead.afterCheckpoint
  rw [JGx_SdkConstants.proofStart,bind_tc_ok,proofLength]
  have checked : Usize.checked_add 688#usize 57607#usize=some 58295#usize := AspisR1.AdapterRw.Scalar.checked_add_eq _ _ _ (by scalar_tac)
  simp only [lift,checked,bind_tc_ok,core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch]
  rw [rawLength]
  simp only [show (58295#usize !=58295#usize)=false from by decide,Bool.false_eq_true,ite_false]
  rw [encoder,bind_tc_ok]
  simp only [core.result.Result.map_err,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch]
  rfl
#print axioms source
end AspisR1.JGx_SdkLength
end
