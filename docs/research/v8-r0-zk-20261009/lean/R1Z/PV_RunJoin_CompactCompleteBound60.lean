import R1Z.PV_RunJoin_CompactBound60
set_option autoImplicit false
namespace R1Z.PV_RunJoin_CompactCompleteBound60
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_ResultPost41

theorem encode (logical : Slice U8) (out : alloc.vec.Vec U8) (n : Nat)
    (length : logical.length=32*n) (room : out.length+16*n≤Usize.max) :
    Post (fun pair => pair.2.length≤out.length+16*n)
      (host_compact.compact_values logical out) := by
  unfold host_compact.compact_values
  apply PV_RunJoin_ResultPost41.bind
  intro remainder
  split
  · change out.length≤out.length+16*n
    omega
  · have bound := PV_RunJoin_CompactBound60.loop_bound logical n 0#usize out (by change 0+32*n=logical.length;omega) room
    cases hl : host_compact.compact_values_loop0 logical out 0#usize with
    | fail e => simp only [hl,bind_tc_fail];trivial
    | div => simp only [hl,bind_tc_div];trivial
    | ok pair =>
      rcases pair with ⟨next,pending⟩
      rw [hl] at bound
      simp only [bind_tc_ok,Aeneas.Std.uncurry]
      cases pending with
      | none => exact bound
      | some status => exact bound

#print axioms encode
end R1Z.PV_RunJoin_CompactCompleteBound60
