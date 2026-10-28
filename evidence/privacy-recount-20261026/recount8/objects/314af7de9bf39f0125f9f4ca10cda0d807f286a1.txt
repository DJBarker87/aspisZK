import R1Z.PV_RunJoin_CoefficientRange44
import R1Z.PV_RunJoin_MergeLoop35
set_option autoImplicit false
namespace R1Z.PV_RunJoin_CoefficientDigit444
open Aeneas Aeneas.Std Result ProverRwSuccessCoefficientsSource

def digit (j : Usize) : Usize :=
  Usize.wrapping_shl (Usize.wrapping_shr j 8#u32 &&& 3#usize) 2#u32

theorem body (j out : Usize) :
    transport.Variant.row_loop.body j { start := 4#usize, «end» := 5#usize } out =
      .ok (.cont ({ start := 5#usize, «end» := 5#usize },out ||| digit j)) := by
  have inc : Usize.wrapping_add 4#usize 1#usize = 5#usize := by
    apply UScalar.eq_of_val_eq
    have h := PV_RunJoin_CoefficientRange44.advance_val 4#usize 5#usize (by decide)
    exact h
  have hn : core.iter.range.IteratorRange.next core.iter.range.StepUsize
      { start := 4#usize, «end» := 5#usize } =
      .ok (some 4#usize,{ start := 5#usize, «end» := 5#usize }) := by
    simpa only [PV_RunJoin_CoefficientRange44.next,PV_RunJoin_CoefficientRange44.between,
      PV_RunJoin_CoefficientRange44.advance,inc] using
      PV_RunJoin_CoefficientRange44.next_step 4#usize 5#usize (by decide)
  have lo : (2#usize * 4#usize : Result Usize) = .ok 8#usize  := by
    obtain ⟨z,hz,hv⟩ := WP.spec_imp_exists (Usize.mul_spec (x := 2#usize) (y := 4#usize) (by scalar_tac))
    have he : z = 8#usize := by scalar_tac
    exact hz.trans (congrArg Result.ok he)
  have hi : (2#usize * 1#usize : Result Usize) = .ok 2#usize  := by
    obtain ⟨z,hz,hv⟩ := WP.spec_imp_exists (Usize.mul_spec (x := 2#usize) (y := 1#usize) (by scalar_tac))
    have he : z = 2#usize := by scalar_tac
    exact hz.trans (congrArg Result.ok he)
  have tau : Array.index_usize transport.TAU 4#usize = .ok 1#usize := by rfl
  have cast_lo : UScalar.cast .U32 8#usize = 8#u32 := by
    apply UScalar.eq_of_val_eq
    rw [PV_CB3_WeightsMachine.cast_count 8#usize (by decide)]
    rfl
  have cast_hi : UScalar.cast .U32 2#usize = 2#u32 := by
    apply UScalar.eq_of_val_eq
    rw [PV_CB3_WeightsMachine.cast_count 2#usize (by decide)]
    rfl
  unfold transport.Variant.row_loop.body
  rw [hn]
  simp only [bind_tc_ok,Aeneas.Std.uncurry,lo]
  rw [PV_RunJoin_CheckedShift44.right j 8#usize (by decide)]
  simp only [bind_tc_ok,lift,tau,hi]
  rw [PV_RunJoin_CheckedShift44.left _ 2#usize (by decide)]
  simp only [bind_tc_ok,lift,digit,cast_lo,cast_hi]
#print axioms body
end R1Z.PV_RunJoin_CoefficientDigit444
