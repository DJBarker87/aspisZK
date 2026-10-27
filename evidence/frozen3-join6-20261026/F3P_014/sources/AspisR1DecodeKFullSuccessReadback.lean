import AspisR1DecodeKFullLoopReadback
import AspisR1DecodeKFullLoopPendingFuel

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1DecodeKFullSuccessReadback

open AspisR1DecodeKCanonicalArrayInvariant
open AspisR1DecodeKFullLoopReadback
open AspisR1DecodeKFullLoopPendingFuel

abbrev QM := AspisR1DecodeKFullV10.aspis_core.field.QM31
abbrev DecodeError := AspisR1DecodeKFullV10.r1_wire.Error

private theorem bind_ok_inv {α β : Type} (r : Result α) (f : α → Result β) (y : β)
    (h : Bind.bind r f = Result.ok y) :
    ∃ x, r = Result.ok x ∧ f x = Result.ok y := by
  cases r with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp [Bind.bind] at h
  | div => simp [Bind.bind] at h

private theorem zero_array_canonical {n : Usize} :
    CanonicalArray (Array.repeat n AspisR1DecodeKFullV10.aspis_core.field.QM31.ZERO) := by
  intro j
  simp [Canonical, AspisR1DecodeKFullV10.aspis_core.field.QM31.ZERO,
    AspisR1DecodeKFullV10.aspis_core.field.P]

theorem decode_k_success_readback
    (n : Usize) (self : AspisR1DecodeKFullV10.r1_wire.ValidatedRecord)
    (offset_values : Usize) (out : Array QM n)
    (h : AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.decode_k n self offset_values =
      .ok (.Ok out)) :
    ∃ byte_offset : Usize,
      lift (offset_values.checked_mul 32#usize) = .ok (some byte_offset) ∧
      ∀ j : Fin n, j.val < n.val →
        ∃ q : QM,
          AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.decode_k_value
            { row := self.row, framed := self.framed } byte_offset
            (UScalar.ofNatCore j.val (by have := j.isLt; scalar_tac)) offset_values = .ok (.Ok q) ∧
          out.val[j.val]'(by simpa [out.property] using j.isLt) = q := by
  have hrun := h
  unfold AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.decode_k at hrun
  by_cases hrow : self.row < 14#u8
  · simp only [hrow, if_pos] at hrun
    cases hrun
  · simp only [hrow, if_neg] at hrun
    rcases bind_ok_inv _ _ _ hrun with ⟨offBytes, hoffBytes, hrun⟩
    rcases bind_ok_inv _ _ _ hrun with ⟨offBytesOk, hoffBytesOk, hrun⟩
    rcases bind_ok_inv _ _ _ hrun with ⟨cf0, hcf0, hrun⟩
    cases cf0 with
    | Break residual =>
        cases residual with
        | Ok impossible => cases impossible
        | Err e => cases hrun
    | Continue offset =>
        have hoffBytesOk' : offBytesOk = core.result.Result.Ok offset := by
          cases offBytesOk with
          | Ok x =>
              have hx : x = offset := by
                simpa [core.result.Result.Insts.CoreOpsTry.branch] using hcf0
              cases hx
              rfl
          | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch] at hcf0
        rw [hoffBytesOk'] at hoffBytesOk
        have hoffSome : offBytes = some offset := by
          cases offBytes with
          | none => simp [AspisR1DecodeKFullV10.core.option.Option.ok_or] at hoffBytesOk
          | some x =>
              have hx : x = offset := by
                simpa [AspisR1DecodeKFullV10.core.option.Option.ok_or] using hoffBytesOk
              cases hx
              rfl
        have hoffByteOffset : lift (offset_values.checked_mul 32#usize) =
            .ok (some offset) := by simpa [hoffSome] using hoffBytes
        rcases bind_ok_inv _ _ _ hrun with ⟨lengthBytes, hlengthBytes, hrun⟩
        rcases bind_ok_inv _ _ _ hrun with ⟨lengthResult, hlengthResult, hrun⟩
        rcases bind_ok_inv _ _ _ hrun with ⟨cf1, hcf1, hrun⟩
        cases cf1 with
        | Break residual =>
            cases residual with
            | Ok impossible => cases impossible
            | Err e => cases hrun
        | Continue length =>
            rcases bind_ok_inv _ _ _ hrun with ⟨totalBytes, htotalBytes, hrun⟩
            rcases bind_ok_inv _ _ _ hrun with ⟨totalResult, htotalResult, hrun⟩
            rcases bind_ok_inv _ _ _ hrun with ⟨cf2, hcf2, hrun⟩
            cases cf2 with
            | Break residual =>
                cases residual with
                | Ok impossible => cases impossible
                | Err e => cases hrun
            | Continue total =>
                rcases bind_ok_inv _ _ _ hrun with ⟨payload, hpayload, hrun⟩
                rcases bind_ok_inv _ _ _ hrun with ⟨slice, hslice, hrun⟩
                rcases bind_ok_inv _ _ _ hrun with ⟨sliceResult, hsliceResult, hrun⟩
                rcases bind_ok_inv _ _ _ hrun with ⟨cf3, hcf3, hrun⟩
                cases cf3 with
                | Break residual =>
                    cases residual with
                    | Ok impossible => cases impossible
                    | Err e => cases hrun
                | Continue _ =>
                    rcases bind_ok_inv _ _ _ hrun with ⟨loopResult, hloop, hrun⟩
                    rcases loopResult with ⟨loopOut, pending⟩
                    cases pending with
                    | none =>
                        have hout : loopOut = out := by
                          exact core.result.Result.Ok.inj (Result.ok.inj hrun)
                        subst out
                        have hread := decode_k_loop_readback_fuel n.val self self.row
                          offset_values offset { start := 0#usize, «end» := n }
                          (Array.repeat n AspisR1DecodeKFullV10.aspis_core.field.QM31.ZERO)
                          loopOut (by rfl) (by
                            have hz : (0#usize).val = 0 := by scalar_tac
                            rw [hz]
                            omega)
                          zero_array_canonical (by
                            change ∀ j : Fin n, j.val < (0#usize).val → _
                            have hz : (0#usize).val = 0 := by scalar_tac
                            rw [hz]
                            intro j hj
                            omega) hloop
                        rcases hread with ⟨_, hvalues⟩
                        change ∀ j : Fin n, j.val < n.val →
                          ∃ q : QM,
                            AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.decode_k_value
                              { row := self.row, framed := self.framed } offset
                              (UScalar.ofNatCore j.val (by have := j.isLt; scalar_tac)) offset_values =
                                .ok (.Ok q) ∧
                            loopOut.val[j.val]'(by simpa [loopOut.property] using j.isLt) = q
                          at hvalues
                        exact ⟨offset, hoffByteOffset, hvalues⟩
                    | some loopErr =>
                        change Result.ok loopErr = Result.ok (.Ok out) at hrun
                        have herr : loopErr = .Ok out := Result.ok.inj hrun
                        have hpending := decode_k_loop_pending_error_shape_fuel n.val self
                          self.row offset_values offset { start := 0#usize, «end» := n }
                          (Array.repeat n AspisR1DecodeKFullV10.aspis_core.field.QM31.ZERO)
                          loopOut (some loopErr) (by rfl) (by
                            have hz : (0#usize).val = 0 := by scalar_tac
                            rw [hz]
                            omega)
                          zero_array_canonical hloop
                        rcases hpending with hnone | ⟨e, he⟩
                        · simp at hnone
                        · have he' : loopErr = core.result.Result.Err e := Option.some.inj he
                          rw [he'] at herr
                          cases herr

#print axioms zero_array_canonical
#print axioms decode_k_success_readback
end AspisR1DecodeKFullSuccessReadback
