import R22DecodeValueTotal
import OccupancyRangeTraversal

set_option autoImplicit false
namespace AspisR1.R22DecodeLoopTotal
open Aeneas Aeneas.Std Result ControlFlow
open R22DecodeValueTotal
abbrev Range := core.ops.range.Range Usize

/-- Total extracted loop on a bounded payload. Noncanonical field bytes stop
with an ordinary Rust error. The framing premise is separate from arithmetic. -/
theorem decode_loop_total
    (n : Usize) (self : Record) (row : U8) (offset byteOffset : Usize)
    (bytes : Slice U8)
    (hpayload : AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.payload self = .ok bytes)
    (hbyte : byteOffset.val = 32*offset.val)
    (hend : byteOffset.val + 32*n.val ≤ bytes.val.length)
    (out : Array Q n) :
    ∃ result,
      AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.decode_k_loop self
        { start := 0#usize, «end» := n } row offset byteOffset out = .ok result := by
  have hlen : bytes.val.length ≤ Usize.max := bytes.property
  have hs : WP.spec
      (AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.decode_k_loop self
        { start := 0#usize, «end» := n } row offset byteOffset out) (fun _ => True) := by
    unfold AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.decode_k_loop
    refine loop.spec_decr_nat
      (fun s : Range × Array Q n => n.val - s.1.start.val)
      (fun s => s.1.end = n ∧ s.1.start.val ≤ n.val)
      (fun _ => True)
      (fun s => AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.decode_k_loop.body
        self row offset byteOffset s.1 s.2)
      ({ start := 0#usize, «end» := n }, out) ?_ ⟨rfl, by simp⟩
    rintro ⟨iter, current⟩ ⟨hiterend, hstart⟩
    change iter.end = n at hiterend
    change iter.start.val ≤ n.val at hstart
    by_cases hlt : iter.start.val < iter.end.val
    · obtain ⟨next, hnext, hnextstart, hnextend, _⟩ :=
        OccupancyRangeTraversal.next_step iter hlt
      have hvalue : iter.start.val < n.val := by simpa [hiterend] using hlt
      obtain ⟨r, hr⟩ := decode_value_total { self with row := row }
        byteOffset iter.start offset bytes
        (by simpa [AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.payload] using hpayload)
        (by omega) (by omega) (by omega)
      cases r with
      | Err e =>
        have hbody : AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.decode_k_loop.body
            self row offset byteOffset iter current = .ok (.done (current, some (.Err e))) := by
          simp [AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.decode_k_loop.body,
            hnext, hr, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
        rw [hbody, WP.spec_ok]
        trivial
      | Ok q =>
        obtain ⟨updated, hupdate, _⟩ := WP.spec_imp_exists
          (Array.update_spec current iter.start q (by simpa [current.property] using hvalue))
        have hbody : AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.decode_k_loop.body
            self row offset byteOffset iter current = .ok (.cont (next, updated)) := by
          simp [AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.decode_k_loop.body,
            hnext, hr, core.result.Result.Insts.CoreOpsTry.branch, hupdate]
        rw [hbody, WP.spec_ok]
        change (next.end = n ∧ next.start.val ≤ n.val) ∧
          n.val - next.start.val < n.val - iter.start.val
        exact ⟨⟨hnextend.trans hiterend, by omega⟩, by omega⟩

    · have hnext := OccupancyRangeTraversal.next_done iter (by omega)
      simp only [AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.decode_k_loop.body,
        hnext, bind_tc_ok, WP.spec_ok]
      trivial
  obtain ⟨result, hrun, _⟩ := WP.spec_imp_exists hs
  exact ⟨result, hrun⟩

#print axioms decode_loop_total
end AspisR1.R22DecodeLoopTotal
