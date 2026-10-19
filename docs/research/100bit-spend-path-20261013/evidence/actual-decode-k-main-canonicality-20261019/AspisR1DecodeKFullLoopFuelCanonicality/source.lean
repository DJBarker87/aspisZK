import AspisR1DecodeKFullLoopBodyFrame
import OccupancyRangeTraversal

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1DecodeKFullLoopFuelCanonicality

open AspisR1DecodeKCanonicalArrayInvariant
open AspisR1DecodeKFullLoopBodyFrame

abbrev QM := AspisR1DecodeKFullV10.aspis_core.field.QM31
abbrev Range := core.ops.range.Range Usize
abbrev DecodeError := AspisR1DecodeKFullV10.r1_wire.Error

private abbrev LoopBody {n : Usize}
    (self : AspisR1DecodeKFullV10.r1_wire.ValidatedRecord)
    (i : UScalar UScalarTy.U8) (offset_values byte_offset : Usize) :=
    fun s : Range × Array QM n =>
      AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.decode_k_loop.body
        self i offset_values byte_offset s.1 s.2

theorem decode_k_loop_success_canonical_fuel
    {n : Usize} (fuel : Nat)
    (self : AspisR1DecodeKFullV10.r1_wire.ValidatedRecord)
    (i : UScalar UScalarTy.U8) (offset_values byte_offset : Usize)
    (iter : Range) (out outFinal : Array QM n)
    (pending : Option (core.result.Result (Array QM n) DecodeError))
    (hend : iter.end.val = n.val) (hspan : iter.start.val + fuel = n.val)
    (hout : CanonicalArray out)
    (hrun : AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.decode_k_loop
      self iter i offset_values byte_offset out = .ok (outFinal, pending)) :
    CanonicalArray outFinal := by
  induction fuel generalizing iter out outFinal pending with
  | zero =>
      have hstop : iter.start.val ≥ iter.end.val := by omega
      have hnext := AspisR1.OccupancyRangeTraversal.next_done iter hstop
      have hrunLoop : Aeneas.Std.loop (LoopBody self i offset_values byte_offset)
          (iter, out) = .ok (outFinal, pending) := by
        simpa [AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.decode_k_loop,
          LoopBody, bind_tc_ok] using hrun
      rw [Aeneas.Std.loop.eq_def] at hrunLoop
      have hbody : LoopBody self i offset_values byte_offset (iter, out) =
          .ok (.done (out, none)) := by
        simp [LoopBody, AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.decode_k_loop.body,
          hnext, bind_tc_ok]
      simp only [hbody] at hrunLoop
      have hp := Result.ok.inj hrunLoop
      have hfinal : outFinal = out := (congrArg Prod.fst hp).symm
      rw [hfinal]
      exact hout
  | succ fuel ih =>
      have hlt : iter.start.val < iter.end.val := by omega
      have hactive : iter.start.val < n.val := by omega
      obtain ⟨iter1, hnext, hstart1, hend1, _⟩ :=
        AspisR1.OccupancyRangeTraversal.next_step iter hlt
      have hvalue : iter.start.val < n.val := hactive
      have hspan1 : iter1.start.val + fuel = n.val := by
        rw [hstart1]
        omega
      have hrunLoop : Aeneas.Std.loop (LoopBody self i offset_values byte_offset)
          (iter, out) = .ok (outFinal, pending) := by
        simpa [AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.decode_k_loop,
          LoopBody, bind_tc_ok] using hrun
      rw [Aeneas.Std.loop.eq_def] at hrunLoop
      cases hsource : AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.decode_k_loop.body
          self i offset_values byte_offset iter out with
      | fail e =>
          have hsource' : LoopBody self i offset_values byte_offset (iter, out) = .fail e := by
            simpa [LoopBody] using hsource
          simp only [hsource'] at hrunLoop
          cases hrunLoop
      | div =>
          have hsource' : LoopBody self i offset_values byte_offset (iter, out) = .div := by
            simpa [LoopBody] using hsource
          simp only [hsource'] at hrunLoop
          cases hrunLoop
      | ok cf =>
          cases cf with
          | done result =>
              rcases result with ⟨out1, pending1⟩
              have hsource' : LoopBody self i offset_values byte_offset (iter, out) =
                  .ok (.done (out1, pending1)) := by simpa [LoopBody] using hsource
              simp only [hsource'] at hrunLoop
              have hp := Result.ok.inj hrunLoop
              have hfinal : outFinal = out1 := (congrArg Prod.fst hp).symm
              have hbodyCan := loop_body_shape_preserves_canonical
                self i offset_values byte_offset iter out iter.start iter1
                (.done (out1, pending1)) hactive hvalue hnext hout hsource
              have hdone : out1 = out ∧ CanonicalArray out1 := by simpa using hbodyCan
              rw [hfinal]
              exact hdone.2
          | cont state =>
              rcases state with ⟨iter2, out2⟩
              have hsource' : LoopBody self i offset_values byte_offset (iter, out) =
                  .ok (.cont (iter2, out2)) := by simpa [LoopBody] using hsource
              simp only [hsource'] at hrunLoop
              have hbodyCan := loop_body_shape_preserves_canonical
                self i offset_values byte_offset iter out iter.start iter1
                (.cont (iter2, out2)) hactive hvalue hnext hout hsource
              have hcont : iter2 = iter1 ∧ ∃ q : QM, Canonical q ∧
                  out2 = out.set iter.start q := by simpa using hbodyCan
              rcases hcont with ⟨hiter, q, hq, hout2⟩
              subst iter2
              have hout2Can : CanonicalArray out2 := by
                rw [hout2]
                exact set_canonical_public out iter.start q hout hq
              have hend1val : iter1.end.val = n.val := by rw [hend1, hend]
              have hrec := ih iter1 out2 outFinal pending hend1val hspan1 hout2Can hrunLoop
              exact hrec

#print axioms decode_k_loop_success_canonical_fuel
end AspisR1DecodeKFullLoopFuelCanonicality
