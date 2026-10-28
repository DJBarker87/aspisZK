import NDF_RawStep
import NDF_RawState
set_option autoImplicit false
namespace NDF_RawRun
open Aeneas Aeneas.Std Result ControlFlow

theorem run {N : Usize} (bytes : Slice U8) (offset j : Usize) (out : Array U8 N)
    (fit : offset.val+N.val≤bytes.val.length) (bound : j.val≤N.val)
    (pre : NDF_RawState.Prefix bytes.val offset.val out.val j.val) :
    ∃ final, NDF_ReaderRef.raw_ref_loop bytes offset out j=ok final ∧
      NDF_RawState.Prefix bytes.val offset.val final.val N.val := by
  by_cases active : j.val<N.val
  · obtain ⟨next,value,nextVal,read,step⟩ := NDF_RawStep.step bytes offset j out fit active
    have room : j.val<out.val.length := by have := out.property; omega
    have invariant : NDF_RawState.Prefix bytes.val offset.val (out.set j value).val next.val := by
      rw [nextVal]
      exact NDF_RawState.extend bytes.val out.val offset.val j.val value room pre read
    obtain ⟨final,tail,post⟩ := run bytes offset next (out.set j value) fit (by omega) invariant
    refine ⟨final,?_,post⟩
    unfold NDF_ReaderRef.raw_ref_loop
    conv_lhs => unfold loop
    simpa only [step] using tail
  · have last : j.val=N.val := by omega
    refine ⟨out,?_,?_⟩
    · unfold NDF_ReaderRef.raw_ref_loop
      conv_lhs => unfold loop
      simp only [NDF_RawStep.done_step bytes offset j out (by omega)]
    · simpa only [last] using pre
termination_by N.val-j.val

#print axioms run
end NDF_RawRun
