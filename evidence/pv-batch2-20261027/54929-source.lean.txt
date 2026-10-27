import R1Z.PV_B2_Sampler
set_option autoImplicit false
namespace PV_B2_ReleaseCheck
open Aeneas Aeneas.Std Result ControlFlow
abbrev run := PV_B2_Sampler.host_sampler.low_base_p_digits_loop2
abbrev body := PV_B2_Sampler.host_sampler.low_base_p_digits_loop2.body

theorem step (i : Usize) (h : i < 8#usize) :
    run i = run (Usize.wrapping_add i 1#usize) := by
  unfold run PV_B2_Sampler.host_sampler.low_base_p_digits_loop2
  rw [Aeneas.Std.loop.eq_def]
  simp only [PV_B2_Sampler.host_sampler.low_base_p_digits_loop2.body,h,if_pos,lift,bind_tc_ok]

theorem done (i : Usize) (h : ¬ i < 8#usize) : run i = ok () := by
  unfold run PV_B2_Sampler.host_sampler.low_base_p_digits_loop2
  rw [Aeneas.Std.loop.eq_def]
  simp only [PV_B2_Sampler.host_sampler.low_base_p_digits_loop2.body,h,if_neg,bind_tc_ok]

/-- Release compilation removes assertions but keeps this seven-step empty loop.
It terminates without affecting the full Result of the digit pass. -/
theorem source : run 1#usize = ok () := by
  calc
    run 1#usize = run 2#usize := step 1#usize (by decide)
    _ = run 3#usize := step 2#usize (by decide)
    _ = run 4#usize := step 3#usize (by decide)
    _ = run 5#usize := step 4#usize (by decide)
    _ = run 6#usize := step 5#usize (by decide)
    _ = run 7#usize := step 6#usize (by decide)
    _ = run 8#usize := step 7#usize (by decide)
    _ = ok () := done 8#usize (by decide)
#print axioms step
#print axioms done
#print axioms source
end PV_B2_ReleaseCheck
