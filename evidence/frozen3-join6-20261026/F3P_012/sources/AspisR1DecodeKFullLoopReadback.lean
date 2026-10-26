import AspisR1DecodeKFullLoopBodyValueFrame
import OccupancyRangeTraversal
import AspisR1DecodeKCanonicalArrayInvariant

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1DecodeKFullLoopReadback

open AspisR1DecodeKCanonicalArrayInvariant
open AspisR1DecodeKFullLoopBodyValueFrame

abbrev QM := AspisR1DecodeKFullV10.aspis_core.field.QM31
abbrev Range := core.ops.range.Range Usize
abbrev DecodeError := AspisR1DecodeKFullV10.r1_wire.Error

private abbrev LoopBody {n : Usize}
    (self : AspisR1DecodeKFullV10.r1_wire.ValidatedRecord)
    (i : UScalar UScalarTy.U8) (offset_values byte_offset : Usize) :=
    fun s : Range × Array QM n =>
      AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.decode_k_loop.body
        self i offset_values byte_offset s.1 s.2

private abbrev decodedAt
    (self : AspisR1DecodeKFullV10.r1_wire.ValidatedRecord)
    (i : UScalar UScalarTy.U8) (offset_values byte_offset index : Usize) (q : QM) : Prop :=
    AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.decode_k_value
      { row := i, framed := self.framed } byte_offset index offset_values = .ok (.Ok q)

private abbrev Readback {n : Usize}
    (self : AspisR1DecodeKFullV10.r1_wire.ValidatedRecord)
    (i : UScalar UScalarTy.U8) (offset_values byte_offset : Usize)
    (iter : Range) (out : Array QM n) : Prop :=
    ∀ j : Fin n, j.val < iter.start.val →
      ∃ q : QM, decodedAt self i offset_values byte_offset
        (UScalar.ofNatCore j.val (by have := j.isLt; scalar_tac)) q ∧
        out.val[j.val]'(by simpa [out.property] using j.isLt) = q

theorem decode_k_loop_readback_fuel
    {n : Usize} (fuel : Nat)
    (self : AspisR1DecodeKFullV10.r1_wire.ValidatedRecord)
    (i : UScalar UScalarTy.U8) (offset_values byte_offset : Usize)
    (iter : Range) (out outFinal : Array QM n)
    (hend : iter.end.val = n.val) (hspan : iter.start.val + fuel = n.val)
    (hout : CanonicalArray out) (hvalues : Readback self i offset_values byte_offset iter out)
    (hrun : AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.decode_k_loop
      self iter i offset_values byte_offset out = .ok (outFinal, none)) :
    CanonicalArray outFinal ∧ Readback self i offset_values byte_offset
      { start := n, «end» := n } outFinal := by
  induction fuel generalizing iter out outFinal with
  | zero =>
      have hstop : iter.start.val ≥ iter.end.val := by omega
      have hnext := AspisR1.OccupancyRangeTraversal.next_done iter hstop
      have hrunLoop : Aeneas.Std.loop (LoopBody self i offset_values byte_offset)
          (iter, out) = .ok (outFinal, none) := by
        simpa [AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.decode_k_loop,
          LoopBody, bind_tc_ok] using hrun
      rw [Aeneas.Std.loop.eq_def] at hrunLoop
      have hbody : LoopBody self i offset_values byte_offset (iter, out) =
          .ok (.done (out, none)) := by
        simp [LoopBody, AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.decode_k_loop.body,
          hnext, bind_tc_ok]
      simp only [hbody] at hrunLoop
      have hp := Result.ok.inj hrunLoop
      have houtEq : outFinal = out := (congrArg Prod.fst hp).symm
      have hstart : iter.start.val = n.val := by omega
      have hcan : CanonicalArray outFinal := by rw [houtEq]; exact hout
      have hvaluesFinal : Readback self i offset_values byte_offset
          { start := n, «end» := n } outFinal := by
        change ∀ j : Fin n, j.val < n.val → _
        intro j hj
        have hjIter : j.val < iter.start.val := by omega
        obtain ⟨q, hdecode, hget⟩ := hvalues j hjIter
        have hget' : outFinal.val[j.val]'(by simpa [outFinal.property] using j.isLt) = q := by
          simpa [houtEq] using hget
        exact ⟨q, hdecode, hget'⟩
      exact ⟨hcan, hvaluesFinal⟩
  | succ fuel ih =>
      have hlt : iter.start.val < iter.end.val := by omega
      have hactive : iter.start.val < n.val := by omega
      obtain ⟨iter1, hnext, hstart1, hend1, _⟩ :=
        AspisR1.OccupancyRangeTraversal.next_step iter hlt
      have hspan1 : iter1.start.val + fuel = n.val := by rw [hstart1]; omega
      have hrunLoop : Aeneas.Std.loop (LoopBody self i offset_values byte_offset)
          (iter, out) = .ok (outFinal, none) := by
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
              have hpend : pending1 = none := congrArg Prod.snd hp
              have hshape := loop_body_shape_preserves_canonical
                self i offset_values byte_offset iter out iter.start iter1
                (.done (out1, pending1)) hactive hactive hnext hout hsource
              have hdone : out1 = out ∧ CanonicalArray out1 ∧
                  ∃ e : DecodeError, pending1 = some (core.result.Result.Err e) := by
                simpa using hshape
              rcases hdone with ⟨_, _, e, he⟩
              rw [he] at hpend
              cases hpend
          | cont state =>
              rcases state with ⟨iter2, out2⟩
              have hsource' : LoopBody self i offset_values byte_offset (iter, out) =
                  .ok (.cont (iter2, out2)) := by simpa [LoopBody] using hsource
              simp only [hsource'] at hrunLoop
              have hshape := loop_body_shape_preserves_canonical
                self i offset_values byte_offset iter out iter.start iter1
                (.cont (iter2, out2)) hactive hactive hnext hout hsource
              have hcont : iter2 = iter1 ∧ ∃ q : QM,
                  decodedAt self i offset_values byte_offset iter.start q ∧
                  Canonical q ∧ out2 = out.set iter.start q := by exact hshape
              rcases hcont with ⟨hiter, q, hdecode, hq, hset⟩
              subst iter2
              have hout2 : CanonicalArray out2 := by
                rw [hset]
                exact set_canonical_public out iter.start q hout hq
              have hvalues2 : Readback self i offset_values byte_offset iter1 out2 := by
                intro j hj
                have hjbound : j.val < n.val := by omega
                have hjold : j.val < iter.start.val ∨ j.val = iter.start.val := by
                  rw [hstart1] at hj
                  omega
                rcases hjold with hjold | hjEq
                · obtain ⟨qj, hdj, hgetj⟩ := hvalues j hjold
                  have hne : j.val ≠ iter.start.val := by omega
                  have hjSet : j.val < (out.val.set iter.start.val q).length := by
                    simpa using j.isLt
                  have hsetRead : (out.val.set iter.start.val q)[j.val]'hjSet =
                      out.val[j.val]'(by simpa [out.property] using j.isLt) := by
                    exact List.getElem_set_ne (l := out.val) (i := iter.start.val) (j := j.val)
                      (by omega) hjSet
                  have hsetVal : out2.val = out.val.set iter.start.val q := by
                    have h := congrArg (fun a : Array QM n => a.val) hset
                    simpa [Array.set_val_eq] using h
                  have hget2 : out2.val[j.val]'(by simpa [out2.property] using j.isLt) = qj := by
                    simpa [hsetVal, hsetRead] using hgetj
                  exact ⟨qj, hdj, hget2⟩
                · have hidx : UScalar.ofNatCore j.val (by have := j.isLt; scalar_tac) = iter.start := by
                    apply UScalar.eq_of_val_eq
                    simp [hjEq]
                  have hdecodeJ : decodedAt self i offset_values byte_offset
                      (UScalar.ofNatCore j.val (by have := j.isLt; scalar_tac)) q := by
                    simpa [hidx] using hdecode
                  have hjSet : j.val < (out.val.set iter.start.val q).length := by
                    simpa using j.isLt
                  have hself : (out.val.set iter.start.val q)[j.val]'hjSet = q := by
                    have hself0 := List.getElem_set_self (l := out.val)
                      (i := iter.start.val) (a := q) (by simpa [hjEq] using hjSet)
                    simpa [hjEq] using hself0
                  have hsetVal : out2.val = out.val.set iter.start.val q := by
                    have h := congrArg (fun a : Array QM n => a.val) hset
                    simpa [Array.set_val_eq] using h
                  have hget2 : out2.val[j.val]'(by simpa [out2.property] using j.isLt) = q := by
                    simpa [hsetVal] using hself
                  exact ⟨q, hdecodeJ, hget2⟩
              have hend1val : iter1.end.val = n.val := by rw [hend1, hend]
              have hrunRec : AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.decode_k_loop
                  self iter1 i offset_values byte_offset out2 = .ok (outFinal, none) := by
                exact hrunLoop
              have hrec := ih iter1 out2 outFinal hend1val hspan1 hout2 hvalues2 hrunRec
              rcases hrec with ⟨hcan, hvaluesFinal⟩
              have hcanFinal : CanonicalArray outFinal := hcan
              have hvaluesFinal' : Readback self i offset_values byte_offset
                  { start := n, «end» := n } outFinal := hvaluesFinal
              exact ⟨hcanFinal, hvaluesFinal'⟩

#print axioms decode_k_loop_readback_fuel
end AspisR1DecodeKFullLoopReadback
