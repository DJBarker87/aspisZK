import R1Z.PV_RunJoin_CompactStep39
set_option autoImplicit false
namespace R1Z.PV_RunJoin_CompactLoop39
open Aeneas Aeneas.Std Result ProverRwFull

def payload (logical : Slice U8) (start : Nat) : Nat → List U8
  | 0 => []
  | n+1 => (logical.val.drop start).take 16 ++ payload logical (start+32) n

/-- Entire source compacting loop, not just its successful-return projection.
The invariant is byte-level canonicality of every reached cell. -/
theorem complete (logical : Slice U8) (n : Nat) (at1 : Usize) (out : alloc.vec.Vec U8)
    (bound : at1.val+32*n=logical.length) (aligned : at1.val%32=0)
    (room : out.length+16*n≤Usize.max)
    (zero : ∀ pos : Usize, pos.val%32=0 → pos.val+32≤logical.length →
      ∀ j : Usize, 16≤j.val → j.val<32 →
        Slice.index_usize logical (Usize.wrapping_add pos j)=.ok 0#u8) :
    ∃ next, host_compact.compact_values_loop0 logical out at1=.ok (next,none) ∧
      next.val=out.val ++ payload logical at1.val n := by
  induction n generalizing at1 out with
  | zero =>
    refine ⟨out,?_,by simp only [payload,List.append_nil]⟩
    unfold host_compact.compact_values_loop0
    rw [ProverRw19LoopBind.loop_bind]
    simp only [PV_RunJoin_CompactStep39.stop logical out at1 (by omega),bind_tc_ok]
  | succ n ih =>
    have cap : logical.length≤Usize.max := logical.property
    have hb : at1.val+32≤logical.length := by omega
    have plus : (Usize.wrapping_add at1 32#usize).val=at1.val+32 := PV_RunJoin_CompactStep39.offset at1 32#usize (by change at1.val+32≤Usize.max;omega)
    obtain ⟨mid,hm,hv⟩ := PV_RunJoin_CompactStep39.step logical out at1 hb (by omega)
      (zero at1 aligned hb)
    have hlen : mid.length=out.length+16 := by
      change mid.val.length=out.val.length+16
      rw [hv,List.length_append,List.length_take,List.length_drop]
      change out.val.length+min 16 (logical.length-at1.val)=out.val.length+16
      rw [Nat.min_eq_left (by omega)]
    obtain ⟨next,hn,hval⟩ := ih (Usize.wrapping_add at1 32#usize) mid
      (by rw [plus];omega) (by rw [plus];omega) (by rw [hlen];omega)
    refine ⟨next,?_,?_⟩
    · unfold host_compact.compact_values_loop0
      rw [ProverRw19LoopBind.loop_bind]
      dsimp only
      rw [hm]
      simp only [bind_tc_ok]
      exact hn
    · rw [hval,hv,plus,payload,List.append_assoc]

#print axioms complete
end R1Z.PV_RunJoin_CompactLoop39
