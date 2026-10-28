import R1Z.PV_RunJoin_PointArray34
import R1Z.ProverRw19LoopBind
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SampleTailStep34
open Aeneas Aeneas.Std Result ProverRwFull
open ProverCommitSampleBits49
abbrev Raw := ProverCommitPrimitive47.Old.Q
variable [ExternalTypes]

theorem bit_result (ops : ExternalFuns) (rem off a : Usize)
    (ho : off.val<rem.val) (hr : rem.val≤9) :
    (if (Usize.wrapping_shr a (UScalar.cast .U32 (Usize.wrapping_sub
        (Usize.wrapping_sub rem 1#usize) off)) &&& 1#usize)=0#usize
      then @aspis_core.field.QM31.ZERO _ (ProverRwDictionaryScalar.selected ops)
      else @aspis_core.field.QM31.ONE _ (ProverRwDictionaryScalar.selected ops)) =
      .ok (PV_RunJoin_FieldData34.source (ProverCommitSampleTail49.qbit a rem.val off.val)) := by
  have hcond := condition rem off a ho hr
  cases hb : bit a rem.val off.val
  · rw [if_pos (hcond.mpr hb),ProverCommitSampleTail49.qbit,hb]
    change Result.ok (ProverRwDictionaryTower.fromQ AspisR1ProducerRelease47.field.QM31.ZERO) = _
    rw [ProverCommitQArray48.source_zero]
    rfl
  · have hn : ¬(Usize.wrapping_shr a (UScalar.cast .U32 (Usize.wrapping_sub
        (Usize.wrapping_sub rem 1#usize) off)) &&& 1#usize)=0#usize := by
      intro h
      have hf := hcond.mp h
      rw [hb] at hf
      cases hf
    rw [if_neg hn,ProverCommitSampleTail49.qbit,hb]
    change Result.ok (ProverRwDictionaryTower.fromQ AspisR1ProducerRelease47.field.QM31.ONE) = _
    rw [ProverCommitSampleTail49.source_one]
    rfl

theorem increment (off : Usize) (ho : off.val<9) :
    (Usize.wrapping_add off 1#usize).val=off.val+1 := by
  simpa only [show (1#usize).val=1 from rfl] using
    ProverCommitBasisFillValue47.add_val off 1#usize (by change off.val+1<2048;omega)

theorem index_value (r off : Usize) (hr : r.val<10) (ho : off.val≤9) :
    (Usize.wrapping_add (Usize.wrapping_add r 1#usize) off).val=r.val+1+off.val := by
  have first : (Usize.wrapping_add r 1#usize).val=r.val+1 := by
    simpa only [show (1#usize).val=1 from rfl] using
      ProverCommitBasisFillValue47.add_val r 1#usize (by change r.val+1<2048;omega)
  rw [ProverCommitBasisFillValue47.add_val _ _ (by rw [first];omega),first]

/-- Actual emitted Boolean-tail step at every in-range sumcheck round,
including its complete Result and its exact updated nominal point array. -/
theorem step (ops : ExternalFuns) (p : Nat → Raw) (r rem a off : Usize)
    (hr : r.val<10) (hrem : rem.val=9-r.val) (ho : off.val<rem.val) :
    @host_sumcheck.evaluate_assignment_loop.body _ (ProverRwDictionaryScalar.selected ops)
      r rem a (PV_RunJoin_PointArray34.array p) off =
      .ok (.cont (PV_RunJoin_PointArray34.array (Function.update p (r.val+1+off.val)
        (ProverCommitSampleTail49.qbit a rem.val off.val)),Usize.wrapping_add off 1#usize)) := by
  have hidx := index_value r off hr (by omega)
  unfold host_sumcheck.evaluate_assignment_loop.body
  simp only [show off<rem from ho,if_true,lift,bind_tc_ok]
  rw [bit_result ops rem off a ho (by omega)]
  simp only [bind_tc_ok]
  rw [PV_RunJoin_PointArray34.update p _ (by rw [hidx];omega)]
  simp only [bind_tc_ok,hidx]

#print axioms bit_result
#print axioms increment
#print axioms index_value
#print axioms step
end R1Z.PV_RunJoin_SampleTailStep34
