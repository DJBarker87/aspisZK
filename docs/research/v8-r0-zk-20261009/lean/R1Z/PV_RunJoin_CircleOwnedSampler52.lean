import R1Z.PV_RunJoin_CircleOwnedOp2152
import R1Z.PV_RunJoin_CircleRawSampler52
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleOwnedSampler52
open PV_RunJoin_CircleOwnedCarrier52
theorem s0 (rank : Array Std.U32 8#usize) (remainder : Std.U64) (j : Std.Usize) :
    PV_AL_CircleOwned.shipped_sampler.qm31_div_pass_loop.body rank remainder j = PV_RunJoin_CircleRawSampler52.shipped_sampler.qm31_div_pass_loop.body rank remainder j := by
  unfold PV_AL_CircleOwned.shipped_sampler.qm31_div_pass_loop.body PV_RunJoin_CircleRawSampler52.shipped_sampler.qm31_div_pass_loop.body
  simp only [PV_RunJoin_CircleOwnedScalar52.f0]
  all_goals rfl

theorem s1 (rank : Array Std.U32 8#usize) (remainder : Std.U64) (j : Std.Usize) :
    PV_AL_CircleOwned.shipped_sampler.qm31_div_pass_loop rank remainder j = PV_RunJoin_CircleRawSampler52.shipped_sampler.qm31_div_pass_loop rank remainder j := by
  unfold PV_AL_CircleOwned.shipped_sampler.qm31_div_pass_loop PV_RunJoin_CircleRawSampler52.shipped_sampler.qm31_div_pass_loop
  simp only [s0]
  all_goals rfl

theorem s2 (rank : Array Std.U32 8#usize) :
    PV_AL_CircleOwned.shipped_sampler.qm31_div_pass rank = PV_RunJoin_CircleRawSampler52.shipped_sampler.qm31_div_pass rank := by
  unfold PV_AL_CircleOwned.shipped_sampler.qm31_div_pass PV_RunJoin_CircleRawSampler52.shipped_sampler.qm31_div_pass
  simp only [s1]
  all_goals rfl

theorem s3 (block : Array Std.U8 32#usize) (rank : Array Std.U32 8#usize)
  (i : Std.Usize) :
    PV_AL_CircleOwned.shipped_sampler.qm31_digits_loop0.body block rank i = PV_RunJoin_CircleRawSampler52.shipped_sampler.qm31_digits_loop0.body block rank i := by
  unfold PV_AL_CircleOwned.shipped_sampler.qm31_digits_loop0.body PV_RunJoin_CircleRawSampler52.shipped_sampler.qm31_digits_loop0.body
  all_goals rfl

theorem s4 (block : Array Std.U8 32#usize) (rank : Array Std.U32 8#usize)
  (i : Std.Usize) :
    PV_AL_CircleOwned.shipped_sampler.qm31_digits_loop0 block rank i = PV_RunJoin_CircleRawSampler52.shipped_sampler.qm31_digits_loop0 block rank i := by
  unfold PV_AL_CircleOwned.shipped_sampler.qm31_digits_loop0 PV_RunJoin_CircleRawSampler52.shipped_sampler.qm31_digits_loop0
  simp only [s3]
  all_goals rfl

theorem s5 (rank : Array Std.U32 8#usize) (digits : Array Std.U32 4#usize)
  (i : Std.Usize) :
    PV_AL_CircleOwned.shipped_sampler.qm31_digits_loop1.body rank digits i = PV_RunJoin_CircleRawSampler52.shipped_sampler.qm31_digits_loop1.body rank digits i := by
  unfold PV_AL_CircleOwned.shipped_sampler.qm31_digits_loop1.body PV_RunJoin_CircleRawSampler52.shipped_sampler.qm31_digits_loop1.body
  simp only [s2]
  all_goals rfl

theorem s6 (rank : Array Std.U32 8#usize) (digits : Array Std.U32 4#usize)
  (i : Std.Usize) :
    PV_AL_CircleOwned.shipped_sampler.qm31_digits_loop1 rank digits i = PV_RunJoin_CircleRawSampler52.shipped_sampler.qm31_digits_loop1 rank digits i := by
  unfold PV_AL_CircleOwned.shipped_sampler.qm31_digits_loop1 PV_RunJoin_CircleRawSampler52.shipped_sampler.qm31_digits_loop1
  simp only [s5]
  all_goals rfl

theorem s7 (block : Array Std.U8 32#usize) :
    PV_AL_CircleOwned.shipped_sampler.qm31_digits block = PV_RunJoin_CircleRawSampler52.shipped_sampler.qm31_digits block := by
  unfold PV_AL_CircleOwned.shipped_sampler.qm31_digits PV_RunJoin_CircleRawSampler52.shipped_sampler.qm31_digits
  simp only [s4,s6]
  all_goals rfl

theorem s8 (block : Array Std.U8 32#usize) :
    PV_AL_CircleOwned.shipped_sampler.qm31_sample block = (do let x ← PV_RunJoin_CircleRawSampler52.shipped_sampler.qm31_sample block; ok (encQ x)) := by
  unfold PV_AL_CircleOwned.shipped_sampler.qm31_sample PV_RunJoin_CircleRawSampler52.shipped_sampler.qm31_sample
  simp only [s7,PV_RunJoin_CircleOwnedOps52.op3,bind_assoc_eq,bind_tc_ok,encQ]
  all_goals rfl

#print axioms s0
#print axioms s1
#print axioms s2
#print axioms s3
#print axioms s4
#print axioms s5
#print axioms s6
#print axioms s7
#print axioms s8
end R1Z.PV_RunJoin_CircleOwnedSampler52
