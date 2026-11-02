import R1Z.PV_RunJoin_PolyChannelsTotal72
set_option autoImplicit false
namespace R1Z.PV_RunJoin_PolyBlockTotal72
open Aeneas Aeneas.Std Result PV_B3_Copy_117 PV_RunJoin_MaskFieldTotal69

theorem complete (polynomial : Array Q 28#usize) (powers : Array Q 3#usize)
    (block : Usize) (bound : block.val≤6) :
    ∃ out,host_arithmetic.evaluate_state_only_polynomial.block_value polynomial powers block=ok out := by
  have hsize : 2^32≤UScalar.size .Usize := by
    rw [UScalar.size_def]
    exact Nat.pow_le_pow_right (by decide) System.Platform.le_numBits
  have bits : 28<UScalar.size .Usize := lt_of_lt_of_le (by decide : 28<2^32) hsize
  let start := Usize.wrapping_mul 4#usize block
  have hs : start.val=4*block.val := by
    unfold start
    rw [Usize.wrapping_mul_val_eq]
    change (4*block.val)%UScalar.size .Usize=4*block.val
    apply Nat.mod_eq_of_lt
    omega
  have offset (k : Usize) (hk : k.val≤3) : (Usize.wrapping_add start k).val<28 := by
    rw [Usize.wrapping_add_val_eq]
    change (start.val+k.val)%UScalar.size .Usize<28
    rw [Nat.mod_eq_of_lt (by omega : start.val+k.val<UScalar.size .Usize)]
    omega
  obtain ⟨q,hq⟩ := ProverRwP6ArrayRead.read polynomial start (by change start.val<28;omega)
  obtain ⟨q1,hq1⟩ := ProverRwP6ArrayRead.read polynomial (Usize.wrapping_add start 1#usize) (offset _ (by decide))
  obtain ⟨q2,hq2⟩ := ProverRwP6ArrayRead.read polynomial (Usize.wrapping_add start 2#usize) (offset _ (by decide))
  obtain ⟨q3,hq3⟩ := ProverRwP6ArrayRead.read polynomial (Usize.wrapping_add start 3#usize) (offset _ (by decide))
  dsimp only [start] at hq hq1 hq2 hq3
  obtain ⟨q4,hq4⟩ := PV_RunJoin_PolyChannelsTotal72.complete powers (Array.make 3#usize [q1,q2,q3])
  obtain ⟨out,ho⟩ := qadd q q4
  exact ⟨out,by simp only [host_arithmetic.evaluate_state_only_polynomial.block_value,
    lift,bind_tc_ok,hq,hq1,hq2,hq3,hq4,ho]⟩

#print axioms complete
end R1Z.PV_RunJoin_PolyBlockTotal72
