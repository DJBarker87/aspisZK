import R1Z.PV_L2_F5DivStep
set_option autoImplicit false
namespace R1Z.PV_L2_F5DivPass
open Aeneas Aeneas.Std Result ControlFlow AspisR1Post25Sampler
open R1Z.PV_L2_Record R1Z.PV_L2_F5DivStep
local instance : Bind Recorded := ⟨@PV_L2_RecordCompact.bind⟩

theorem unroll (rank : Array U32 8#usize) (remainder : U64) (j : Usize) :
    sampler.qm31_div_pass_loop rank remainder j = if j>0#usize then (do
      let after ← step rank remainder j
      sampler.qm31_div_pass_loop after.1 after.2.1 after.2.2) else ok (rank,remainder) := by
  rw [sampler.qm31_div_pass_loop,loop]
  simp only [Aeneas.Std.uncurry_apply_pair]
  rw [source_body]
  by_cases h : j>0#usize
  · simp only [if_pos h]
    cases hs : step rank remainder j <;> rfl
  · simp only [if_neg h]

def execute : Nat → Array U32 8#usize → U64 → Usize → Recorded (Array U32 8#usize × U64)
  | 0,rank,remainder,j => if j>0#usize then ⟨.div,[.guard 204 j.val 0 true]⟩
    else ⟨ok (rank,remainder),[.guard 204 j.val 0 false]⟩
  | fuel+1,rank,remainder,j => if j>0#usize then do
      let _ ← operation (.guard 204 j.val 0 true) (ok ())
      let after ← PV_L2_F5DivStep.recorded rank remainder j
      execute fuel after.1 after.2.1 after.2.2
    else ⟨ok (rank,remainder),[.guard 204 j.val 0 false]⟩

theorem erases (fuel : Nat) (rank : Array U32 8#usize) (remainder : U64) (j : Usize)
    (enough : j.val≤fuel) :
    (execute fuel rank remainder j).value = sampler.qm31_div_pass_loop rank remainder j := by
  induction fuel generalizing rank remainder j with
  | zero =>
    have hn : ¬j>0#usize := by scalar_tac
    rw [execute,if_neg hn,unroll,if_neg hn]
  | succ fuel ih =>
    rw [execute,unroll]
    by_cases h : j>0#usize
    · rw [if_pos h,if_pos h]
      simp only [PV_L2_RecordCompact.bind_value,operation_value,bind_tc_ok,
        PV_L2_F5DivStep.erases]
      cases hs : step rank remainder j with
      | fail e => rfl
      | div => rfl
      | ok after =>
        simp only [bind_tc_ok]
        exact ih after.1 after.2.1 after.2.2 (by have := decrease rank remainder j after hs;omega)
    · rw [if_neg h,if_neg h]

def pass (rank : Array U32 8#usize) : Recorded (Array U32 8#usize × U32) := do
  let (rank1,remainder) ← execute 8 rank 0#u64 8#usize
  PV_L2_Record.pure (rank1,UScalar.cast .U32 remainder)

theorem pass_erases (rank : Array U32 8#usize) :
    (pass rank).value = sampler.qm31_div_pass rank := by
  simp only [pass,sampler.qm31_div_pass,PV_L2_RecordCompact.bind_value,
    erases 8 rank 0#u64 8#usize (by decide),PV_L2_Record.pure_value,lift,bind_tc_ok]

#print axioms unroll
#print axioms erases
#print axioms pass_erases
end R1Z.PV_L2_F5DivPass
