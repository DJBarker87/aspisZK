import R1Z.PV_RunJoin_CompactLoop39
set_option autoImplicit false
namespace R1Z.PV_RunJoin_CompactComplete39
open Aeneas Aeneas.Std Result ProverRwFull

/-- Complete compact_values Result on a whole number of canonical logical
cells. No compaction-success premise is assumed. Native allocation effects
and the association of caller bytes with these cells remain separate. -/
theorem encode (logical : Slice U8) (out : alloc.vec.Vec U8) (n : Nat)
    (length : logical.length=32*n) (room : out.length+16*n≤Usize.max)
    (zero : ∀ pos : Usize, pos.val%32=0 → pos.val+32≤logical.length →
      ∀ j : Usize, 16≤j.val → j.val<32 →
        Slice.index_usize logical (Usize.wrapping_add pos j)=.ok 0#u8) :
    ∃ next, host_compact.compact_values logical out=.ok (.Ok (),next) ∧
      next.val=out.val ++ PV_RunJoin_CompactLoop39.payload logical 0 n := by
  obtain ⟨r,hr,hv⟩ := WP.spec_imp_exists
    (UScalar.rem_spec (Slice.len logical) (y := 32#usize) (by decide))
  have rz : r=0#usize := by
    apply UScalar.eq_of_val_eq
    change r.val=0
    have hz : (Slice.len logical).val=32*n := length
    change r.val=(Slice.len logical).val%32 at hv
    rw [hz] at hv
    omega
  rw [rz] at hr
  obtain ⟨next,hn,hval⟩ := PV_RunJoin_CompactLoop39.complete logical n 0#usize out
    (by change 0+32*n=logical.length;omega) rfl room zero
  refine ⟨next,?_,hval⟩
  unfold host_compact.compact_values
  dsimp only
  rw [hr]
  simp only [bind_tc_ok,show ¬(0#usize != 0#usize) from (by decide),↓reduceIte,hn]
  rfl

#print axioms encode
end R1Z.PV_RunJoin_CompactComplete39
