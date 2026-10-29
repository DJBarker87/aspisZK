import R1Z.PV_RunJoin_CompactLoop39
import R1Z.PV_RunJoin_ResultPost41
set_option autoImplicit false
namespace R1Z.PV_RunJoin_CompactBound60
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_ResultPost41

/-- Bound every successful partial compaction, including an early high-byte
rejection. No canonicality or successful codec premise is assumed. -/
theorem loop_bound (logical : Slice U8) (n : Nat) (at1 : Usize) (out : alloc.vec.Vec U8)
    (bound : at1.val+32*n=logical.length)
    (room : out.length+16*n≤Usize.max) :
    Post (fun pair => pair.1.length≤out.length+16*n)
      (host_compact.compact_values_loop0 logical out at1) := by
  induction n generalizing at1 out with
  | zero =>
    unfold host_compact.compact_values_loop0
    rw [ProverRw19LoopBind.loop_bind]
    simp only [PV_RunJoin_CompactStep39.stop logical out at1 (by omega),bind_tc_ok]
    change out.length≤out.length+16*0
    omega
  | succ n ih =>
    have cap : logical.length≤Usize.max := logical.property
    have more : at1<Slice.len logical := by change at1.val<logical.length; omega
    have plus16 := PV_RunJoin_CompactStep39.offset at1 16#usize (by change at1.val+16≤Usize.max;omega)
    have plus32 := PV_RunJoin_CompactStep39.offset at1 32#usize (by change at1.val+32≤Usize.max;omega)
    obtain ⟨s,mid,hs,hm,hval⟩ := PV_RunJoin_ByteRange39.append logical out at1
      (Usize.wrapping_add at1 16#usize) (by rw [plus16];omega)
      (by rw [plus16];omega) (by rw [plus16];change out.length+(_-at1.val)≤_;omega)
    have hlen : mid.length=out.length+16 := by
      change mid.val.length=out.val.length+16
      rw [hval,List.length_append,List.length_take,List.length_drop,plus16]
      have hlog : logical.val.length=logical.length := rfl
      omega
    unfold host_compact.compact_values_loop0
    rw [ProverRw19LoopBind.loop_bind]
    simp only [host_compact.compact_values_loop0.body,more,if_true]
    rw [bind_assoc_eq]
    apply PV_RunJoin_ResultPost41.bind
    intro pending
    cases pending with
    | some status =>
      simp only [bind_tc_ok]
      change out.length≤out.length+16*(n+1)
      omega
    | none =>
      simp only [lift,bind_tc_ok,hs,hm]
      have htail := ih (Usize.wrapping_add at1 32#usize) mid
        (by rw [plus32];omega) (by rw [hlen];omega)
      exact fun_pair_bound htail hlen
where
  fun_pair_bound {logical : Slice U8} {at1 : Usize} {out mid : alloc.vec.Vec U8} {n : Nat}
      (h : Post (fun pair => pair.1.length≤mid.length+16*n)
        (host_compact.compact_values_loop0 logical mid at1))
      (hlen : mid.length=out.length+16) :
      Post (fun pair => pair.1.length≤out.length+16*(n+1))
        (host_compact.compact_values_loop0 logical mid at1) := by
    cases host_compact.compact_values_loop0 logical mid at1 with
    | fail e => trivial
    | div => trivial
    | ok pair => change pair.1.length≤_ at h ⊢;omega

#print axioms loop_bound
end R1Z.PV_RunJoin_CompactBound60
