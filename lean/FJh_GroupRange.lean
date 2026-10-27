import FJh_Base
import Aeneas.Std.WP

set_option autoImplicit false
namespace AspisR1.FJh_GroupRange
open Aeneas Aeneas.Std Result WP

theorem group_range_success (group : Usize) (hg : group.val < 4) :
    ∃ start finish : Usize,
      (do let start ← 4#usize * group
          let finish ← start + 4#usize
          ok (start, finish)) = .ok (start, finish) ∧
      start.val = 4 * group.val ∧ finish.val = 4 * group.val + 4 ∧
      finish.val ≤ 16 := by
  have hmax := Usize.cMax_bound_concrete.1
  have hmul : (4#usize * group : Result Usize) ⦃ z => z.val = 4 * group.val ⦄ := by
    apply UScalar.mul_spec
    scalar_tac
  obtain ⟨start, hmulRun, hstart⟩ := WP.spec_imp_exists hmul
  have hadd : (start + 4#usize : Result Usize) ⦃ z => z.val = start.val + 4 ⦄ := by
    apply UScalar.add_spec
    scalar_tac
  obtain ⟨finish, haddRun, hfinish⟩ := WP.spec_imp_exists hadd
  refine ⟨start, finish, ?_, hstart, ?_, ?_⟩
  · simp [hmulRun, haddRun, bind_tc_ok]
  · rw [hfinish, hstart]
  · rw [hfinish, hstart]
    omega

#print axioms group_range_success
end AspisR1.FJh_GroupRange
