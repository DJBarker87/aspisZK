import R1Z.PV_RunJoin_CompactHigh39
import R1Z.PV_RunJoin_ByteRange39
set_option autoImplicit false
namespace R1Z.PV_RunJoin_CompactStep39
open Aeneas Aeneas.Std Result ProverRwFull

theorem offset (at1 : Usize) (n : Usize) (bound : at1.val+n.val≤Usize.max) :
    (Usize.wrapping_add at1 n).val=at1.val+n.val := by
  rw [Usize.wrapping_add_val_eq]
  apply Nat.mod_eq_of_lt
  have size := Usize.max_succ_eq_pow
  rw [UScalar.size_def,UScalarTy.Usize_numBits_eq]
  omega

theorem stop (logical : Slice U8) (out : alloc.vec.Vec U8) (at1 : Usize)
    (h : logical.length≤at1.val) :
    host_compact.compact_values_loop0.body logical out at1=.ok (.done (out,none)) := by
  simp only [host_compact.compact_values_loop0.body,
    show ¬at1<Slice.len logical from (by change ¬at1.val<logical.length;omega),↓reduceIte]

/-- One complete logical cell: check all sixteen high bytes before appending
its sixteen low bytes. Bounds discharge all slice and cursor operations. -/
theorem step (logical : Slice U8) (out : alloc.vec.Vec U8) (at1 : Usize)
    (bound : at1.val+32≤logical.length) (room : out.length+16≤Usize.max)
    (zero : ∀ j : Usize, 16≤j.val → j.val<32 →
      Slice.index_usize logical (Usize.wrapping_add at1 j)=.ok 0#u8) :
    ∃ next, host_compact.compact_values_loop0.body logical out at1=
        .ok (.cont (next,Usize.wrapping_add at1 32#usize)) ∧
      next.val=out.val ++ (logical.val.drop at1.val).take 16 := by
  have cap : logical.length≤Usize.max := logical.property
  have plus16 : (Usize.wrapping_add at1 16#usize).val=at1.val+16 := offset at1 16#usize (by change at1.val+16≤Usize.max;omega)
  have hh := PV_RunJoin_CompactHigh39.complete logical at1 16 16#usize rfl (by decide) zero
  obtain ⟨s,next,hs,hn,hval⟩ := PV_RunJoin_ByteRange39.append logical out at1
    (Usize.wrapping_add at1 16#usize) (by rw [plus16];omega)
    (by rw [plus16];omega) (by rw [plus16];simpa only [Nat.add_sub_cancel_left] using room)
  refine ⟨next,?_,?_⟩
  · unfold host_compact.compact_values_loop0.body
    simp only [show at1<Slice.len logical from (by change at1.val<logical.length;omega),
      ↓reduceIte,hh,bind_tc_ok,lift,hs,hn]
  · simpa only [plus16,Nat.add_sub_cancel_left] using hval

#print axioms offset
#print axioms stop
#print axioms step
end R1Z.PV_RunJoin_CompactStep39
