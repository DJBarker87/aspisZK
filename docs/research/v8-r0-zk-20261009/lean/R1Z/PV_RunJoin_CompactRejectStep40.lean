import R1Z.PV_RunJoin_CompactReject39
import R1Z.PV_RunJoin_CompactStep39
set_option autoImplicit false
namespace R1Z.PV_RunJoin_CompactRejectStep40
open Aeneas Aeneas.Std Result ProverRwFull

/-- A malformed cell keeps exactly the prefix output, without appending any
low byte from that cell. All prior high-byte reads are explicit input facts. -/
theorem cell (logical : Slice U8) (out : alloc.vec.Vec U8) (at1 bad : Usize)
    (value : U8) (at_bound : at1.val<logical.length) (bad_lo : 16≤bad.val)
    (bad_hi : bad.val<32) (nonzero : value≠0#u8)
    (read_bad : Slice.index_usize logical (Usize.wrapping_add at1 bad)=.ok value)
    (before_bad : ∀ j : Usize,16≤j.val → j.val<bad.val →
      Slice.index_usize logical (Usize.wrapping_add at1 j)=.ok 0#u8) :
    host_compact.compact_values_loop0.body logical out at1=
      .ok (.done (out,some (.Err compact.CodecError.NonZeroHigh))) := by
  have hh := PV_RunJoin_CompactReject39.high logical at1 bad value bad_hi nonzero read_bad
    (bad.val-16) 16#usize (by change 16+(bad.val-16)=bad.val;omega) before_bad
  simp only [host_compact.compact_values_loop0.body,
    show at1<Slice.len logical from at_bound,↓reduceIte,hh,bind_tc_ok]

theorem loop (logical : Slice U8) (out : alloc.vec.Vec U8) (at1 bad : Usize)
    (value : U8) (at_bound : at1.val<logical.length) (bad_lo : 16≤bad.val)
    (bad_hi : bad.val<32) (nonzero : value≠0#u8)
    (read_bad : Slice.index_usize logical (Usize.wrapping_add at1 bad)=.ok value)
    (before_bad : ∀ j : Usize,16≤j.val → j.val<bad.val →
      Slice.index_usize logical (Usize.wrapping_add at1 j)=.ok 0#u8) :
    host_compact.compact_values_loop0 logical out at1=
      .ok (out,some (.Err compact.CodecError.NonZeroHigh)) := by
  unfold host_compact.compact_values_loop0
  rw [ProverRw19LoopBind.loop_bind]
  simp only [cell logical out at1 bad value at_bound bad_lo bad_hi nonzero read_bad before_bad,bind_tc_ok]
#print axioms cell
#print axioms loop
end R1Z.PV_RunJoin_CompactRejectStep40
