import R1Z.PV_RunJoin_CompactRejectPrefix40
import R1Z.PV_RunJoin_CompactPayload39
set_option autoImplicit false
namespace R1Z.PV_RunJoin_CompactRejectComplete40
open Aeneas Aeneas.Std Result ProverRwFull

/-- Complete compact_values rejection after k good cells. Its exact retained
output is the initial output followed by those k low halves, and has length
out.length+16*k. The bad cell contributes no output bytes. -/
theorem reject (logical : Slice U8) (out : alloc.vec.Vec U8) (total k : Nat)
    (length : logical.length=32*total) (badAt bad : Usize) (value : U8)
    (location : badAt.val=32*k) (cell_bound : badAt.val+32≤logical.length)
    (room : out.length+16*k≤Usize.max) (bad_lo : 16≤bad.val) (bad_hi : bad.val<32)
    (nonzero : value≠0#u8)
    (read_bad : Slice.index_usize logical (Usize.wrapping_add badAt bad)=.ok value)
    (before_bad : ∀ j : Usize,16≤j.val → j.val<bad.val →
      Slice.index_usize logical (Usize.wrapping_add badAt j)=.ok 0#u8)
    (prior : ∀ pos : Usize,pos.val<badAt.val →
      ∀ j : Usize,16≤j.val → j.val<32 →
        Slice.index_usize logical (Usize.wrapping_add pos j)=.ok 0#u8) :
    ∃ next, host_compact.compact_values logical out=.ok (.Err compact.CodecError.NonZeroHigh,next) ∧
      next.val=out.val ++ PV_RunJoin_CompactLoop39.payload logical 0 k ∧
      next.length=out.length+16*k := by
  obtain ⟨next,hn,hbytes⟩ := PV_RunJoin_CompactRejectPrefix40.loop logical badAt bad value
    cell_bound bad_lo bad_hi nonzero read_bad before_bad k 0#usize out
    (by change 0+32*k=badAt.val;omega) room (fun pos _ hb => prior pos hb)
  obtain ⟨r,hr,hv⟩ := WP.spec_imp_exists
    (UScalar.rem_spec (Slice.len logical) (y := 32#usize) (by decide))
  have rz : r=0#usize := by
    apply UScalar.eq_of_val_eq
    have hz : r.val=logical.length%32 := hv
    rw [length] at hz
    change r.val=0
    omega
  rw [rz] at hr
  refine ⟨next,?_,hbytes,?_⟩
  · unfold host_compact.compact_values
    dsimp only
    rw [hr]
    simp only [bind_tc_ok,bne_self_eq_false,Bool.false_eq_true,↓reduceIte,hn]
    rfl
  · change next.val.length=out.val.length+16*k
    rw [hbytes,List.length_append,PV_RunJoin_CompactPayload39.length logical 0 k (by omega)]
#print axioms reject
end R1Z.PV_RunJoin_CompactRejectComplete40
