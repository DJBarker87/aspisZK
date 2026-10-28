import R1Z.PV_RunJoin_CompactRejectStep40
import R1Z.PV_RunJoin_CompactLoop39
set_option autoImplicit false
namespace R1Z.PV_RunJoin_CompactRejectPrefix40
open Aeneas Aeneas.Std Result ProverRwFull

/-- Arbitrarily many valid cells can precede the first bad high byte. The
source retains exactly those compacted cells on rejection. -/
theorem loop (logical : Slice U8) (badAt bad : Usize) (value : U8)
    (cell_bound : badAt.val+32≤logical.length) (bad_lo : 16≤bad.val) (bad_hi : bad.val<32)
    (nonzero : value≠0#u8)
    (read_bad : Slice.index_usize logical (Usize.wrapping_add badAt bad)=.ok value)
    (before_bad : ∀ j : Usize,16≤j.val → j.val<bad.val →
      Slice.index_usize logical (Usize.wrapping_add badAt j)=.ok 0#u8)
    (n : Nat) (at1 : Usize) (out : alloc.vec.Vec U8)
    (bound : at1.val+32*n=badAt.val) (room : out.length+16*n≤Usize.max)
    (prior : ∀ pos : Usize,at1.val≤pos.val → pos.val<badAt.val →
      ∀ j : Usize,16≤j.val → j.val<32 →
        Slice.index_usize logical (Usize.wrapping_add pos j)=.ok 0#u8) :
    ∃ next, host_compact.compact_values_loop0 logical out at1=
      .ok (next,some (.Err compact.CodecError.NonZeroHigh)) ∧
      next.val=out.val ++ PV_RunJoin_CompactLoop39.payload logical at1.val n := by
  induction n generalizing at1 out with
  | zero =>
    have same : at1=badAt := UScalar.eq_of_val_eq (by omega)
    subst at1
    refine ⟨out,PV_RunJoin_CompactRejectStep40.loop logical out badAt bad value
      (by omega) bad_lo bad_hi nonzero read_bad before_bad,?_⟩
    simp only [PV_RunJoin_CompactLoop39.payload,List.append_nil]
  | succ n ih =>
    obtain ⟨mid,hm,hmid⟩ := PV_RunJoin_CompactStep39.step logical out at1
      (by omega) (by omega) (prior at1 (Nat.le_refl _) (by omega))
    have inc : (Usize.wrapping_add at1 32#usize).val=at1.val+32 :=
      PV_RunJoin_CompactStep39.offset at1 32#usize (by
        have cap : logical.length≤Usize.max := logical.property
        change at1.val+32≤Usize.max
        omega)
    have midlen : mid.length=out.length+16 := by
      change mid.val.length=out.val.length+16
      rw [hmid,List.length_append,List.length_take,List.length_drop]
      have hc : badAt.val+32≤logical.val.length := cell_bound
      omega
    obtain ⟨next,hn,hval⟩ := ih (Usize.wrapping_add at1 32#usize) mid
      (by rw [inc];omega) (by rw [midlen];omega)
      (fun pos hp hb => prior pos (by rw [inc] at hp;omega) hb)
    refine ⟨next,?_,?_⟩
    · unfold host_compact.compact_values_loop0
      rw [ProverRw19LoopBind.loop_bind]
      dsimp only
      rw [hm]
      simp only [bind_tc_ok]
      exact hn
    · rw [hval,hmid,inc,PV_RunJoin_CompactLoop39.payload,List.append_assoc]
#print axioms loop
end R1Z.PV_RunJoin_CompactRejectPrefix40
