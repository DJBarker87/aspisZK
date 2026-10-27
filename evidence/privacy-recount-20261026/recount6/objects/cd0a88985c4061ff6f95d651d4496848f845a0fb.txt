import R1Z.ProverRwEffectSource

/-! Symbolic constant-buffer law for the actual emitted OR scan. No concrete
32-iteration kernel replay is used. -/
set_option autoImplicit false
namespace R1Z.ProverRwEffectNonzero
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
variable [ExternalTypes] [ExternalFuns]
abbrev scan := aspis_prover.state_only_entropy.entropy_nonzero32_loop

theorem index_repeat (byte : U8) (i : Usize) (hi : i.val < 32) :
    Array.index_usize (Array.repeat 32#usize byte) i = .ok byte := by
  have hb : i.val < (Array.repeat 32#usize byte).length := by
    simpa [Array.length,Array.repeat] using hi
  obtain ⟨x,hx,hv⟩ := WP.spec_imp_exists (Array.index_usize_spec (Array.repeat 32#usize byte) i hb)
  simpa only [Array.repeat_val,List.getElem_replicate] using hx.trans (congrArg Result.ok hv)

theorem scan_fixed (byte combined : U8) (stable : combined ||| byte = combined)
    (index : Usize) (fuel : Nat) (bound : index.val+fuel=32) :
    scan (Array.repeat 32#usize byte) combined index = .ok combined := by
  unfold scan aspis_prover.state_only_entropy.entropy_nonzero32_loop
  induction fuel generalizing index with
  | zero =>
    have stop : ¬ index < 32#usize := by change ¬ index.val < 32; omega
    rw [loop]
    simp only [aspis_prover.state_only_entropy.entropy_nonzero32_loop.body,stop,if_false,bind_tc_ok]
  | succ fuel ih =>
    have go : index < 32#usize := by change index.val < 32; omega
    have idx : index.val < 32 := by omega
    have add : (Usize.wrapping_add index 1#usize).val = index.val+1 := by
      rw [Usize.wrapping_add_val_eq]
      change (index.val+1) % UScalar.size .Usize = index.val+1
      rw [Nat.mod_eq_of_lt]
      have hs : 32 < UScalar.size .Usize := (32#usize).hSize
      omega
    rw [loop]
    simp only [aspis_prover.state_only_entropy.entropy_nonzero32_loop.body,go,if_true,
      index_repeat byte index idx,bind_tc_ok,stable,lift,bind_tc_ok]
    exact ih (Usize.wrapping_add index 1#usize) (by omega)

theorem nonzero_repeat (byte : U8) (stable : byte ||| byte = byte)
    (initial : (0#u8) ||| byte = byte) :
    aspis_prover.state_only_entropy.entropy_nonzero32 (Array.repeat 32#usize byte) =
      .ok (byte != 0#u8) := by
  unfold aspis_prover.state_only_entropy.entropy_nonzero32
  unfold aspis_prover.state_only_entropy.entropy_nonzero32_loop
  rw [loop]
  have go : (0#usize) < 32#usize := by decide
  simp only [aspis_prover.state_only_entropy.entropy_nonzero32_loop.body,go,if_true,
    index_repeat byte 0#usize (by decide),bind_tc_ok,initial,lift,bind_tc_ok]
  have add0 : Usize.wrapping_add 0#usize 1#usize = 1#usize := by
    apply UScalar.eq_of_val_eq
    rw [Usize.wrapping_add_val_eq]
    change 1 % UScalar.size .Usize = 1
    exact Nat.mod_eq_of_lt (1#usize).hSize
  rw [add0]
  have tail := scan_fixed byte byte stable 1#usize 31 (by rfl)
  change (do let combined ← scan (Array.repeat 32#usize byte) byte 1#usize
             ok (combined != 0#u8)) = _
  rw [tail]
  rfl

#print axioms index_repeat
#print axioms scan_fixed
#print axioms nonzero_repeat
end R1Z.ProverRwEffectNonzero
