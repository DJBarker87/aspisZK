from pathlib import Path
for d,dst in enumerate([3,4,2,0,1]):
 count=2*d;shift=2*dst
 s=f'''import R1Z.PV_RunJoin_CoefficientRange44
import R1Z.PV_RunJoin_MergeLoop35
set_option autoImplicit false
namespace R1Z.PV_RunJoin_CoefficientDigit{d}44
open Aeneas Aeneas.Std Result ProverRwSuccessCoefficientsSource

def digit (j : Usize) : Usize :=
  Usize.wrapping_shl (Usize.wrapping_shr j {count}#u32 &&& 3#usize) {shift}#u32

theorem body (j out : Usize) :
    transport.Variant.row_loop.body j {{ start := {d}#usize, «end» := 5#usize }} out =
      .ok (.cont ({{ start := {d+1}#usize, «end» := 5#usize }},out ||| digit j)) := by
  have inc : Usize.wrapping_add {d}#usize 1#usize = {d+1}#usize := by
    apply UScalar.eq_of_val_eq
    have h := PV_RunJoin_CoefficientRange44.advance_val {d}#usize 5#usize (by decide)
    exact h
  have hn : core.iter.range.IteratorRange.next core.iter.range.StepUsize
      {{ start := {d}#usize, «end» := 5#usize }} =
      .ok (some {d}#usize,{{ start := {d+1}#usize, «end» := 5#usize }}) := by
    simpa only [PV_RunJoin_CoefficientRange44.next,PV_RunJoin_CoefficientRange44.between,
      PV_RunJoin_CoefficientRange44.advance,inc] using
      PV_RunJoin_CoefficientRange44.next_step {d}#usize 5#usize (by decide)
  have lo : (2#usize * {d}#usize : Result Usize) = .ok {count}#usize  := by
    obtain ⟨z,hz,hv⟩ := WP.spec_imp_exists (Usize.mul_spec (x := 2#usize) (y := {d}#usize) (by scalar_tac))
    have he : z = {count}#usize := by scalar_tac
    exact hz.trans (congrArg Result.ok he)
  have hi : (2#usize * {dst}#usize : Result Usize) = .ok {shift}#usize  := by
    obtain ⟨z,hz,hv⟩ := WP.spec_imp_exists (Usize.mul_spec (x := 2#usize) (y := {dst}#usize) (by scalar_tac))
    have he : z = {shift}#usize := by scalar_tac
    exact hz.trans (congrArg Result.ok he)
  have tau : Array.index_usize transport.TAU {d}#usize = .ok {dst}#usize := by rfl
  have cast_lo : UScalar.cast .U32 {count}#usize = {count}#u32 := by
    apply UScalar.eq_of_val_eq
    rw [PV_CB3_WeightsMachine.cast_count {count}#usize (by decide)]
    rfl
  have cast_hi : UScalar.cast .U32 {shift}#usize = {shift}#u32 := by
    apply UScalar.eq_of_val_eq
    rw [PV_CB3_WeightsMachine.cast_count {shift}#usize (by decide)]
    rfl
  unfold transport.Variant.row_loop.body
  rw [hn]
  simp only [bind_tc_ok,Aeneas.Std.uncurry,lo]
  rw [PV_RunJoin_CheckedShift44.right j {count}#usize (by decide)]
  simp only [bind_tc_ok,lift,tau,hi]
  rw [PV_RunJoin_CheckedShift44.left _ {shift}#usize (by decide)]
  simp only [bind_tc_ok,lift,digit,cast_lo,cast_hi]
#print axioms body
end R1Z.PV_RunJoin_CoefficientDigit{d}44
'''
 Path(f'docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RunJoin_CoefficientDigit{d}44.lean').write_text(s)
