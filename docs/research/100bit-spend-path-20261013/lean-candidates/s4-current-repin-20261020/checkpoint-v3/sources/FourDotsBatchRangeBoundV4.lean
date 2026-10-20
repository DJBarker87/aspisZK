import FourDotsBatchInnerCallsV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1FastDotsBatchRangeBound

theorem width_le_four (start batchEndArg rangeEnd : Usize)
    (hstart : start.val < 26)
    (hplus : UScalar.add start 4#usize = .ok batchEndArg)
    (hmin : core.cmp.min core.cmp.OrdUsize batchEndArg 26#usize = .ok rangeEnd) :
    rangeEnd.val - start.val ≤ 4 := by
  have hplusSpec : UScalar.add start 4#usize ⦃z => z.val = start.val + 4⦄ := by
    apply UScalar.add_spec
    scalar_tac
  obtain ⟨z, hz, hzval⟩ := WP.spec_imp_exists hplusSpec
  have hzeq : z = batchEndArg := Result.ok.inj (hz.symm.trans hplus)
  have hpv : batchEndArg.val = start.val + 4 := by rw [← hzeq]; exact hzval
  have hminEq : rangeEnd = if batchEndArg < 26#usize then batchEndArg else 26#usize := by
    simpa [core.cmp.min, core.cmp.OrdUsize, core.cmp.impls.OrdUsize.min] using hmin.symm
  by_cases hlt : batchEndArg < 26#usize
  · rw [if_pos hlt] at hminEq
    rw [hminEq, hpv]
    omega
  · have hge : 26 ≤ batchEndArg.val := by scalar_tac
    rw [if_neg hlt] at hminEq
    have hrange : rangeEnd.val = 26 := by
      simpa using congrArg (fun x : Usize => x.val) hminEq
    omega
#print axioms width_le_four
end AspisR1FastDotsBatchRangeBound
