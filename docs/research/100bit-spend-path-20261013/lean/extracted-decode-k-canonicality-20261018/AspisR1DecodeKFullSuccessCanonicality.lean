import AspisR1DecodeKFullLoopFuelCanonicality
import AspisR1DecodeKFullLoopPendingFuel

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1DecodeKFullSuccessCanonicality

open AspisR1DecodeKCanonicalArrayInvariant
open AspisR1DecodeKFullLoopFuelCanonicality
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

theorem decode_k_success_canonical
    (n : Usize) (self : AspisR1DecodeKFullV10.r1_wire.ValidatedRecord)
    (offset_values : Usize) (out : Array QM n)
    (h : AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.decode_k n self offset_values =
      .ok (.Ok out)) :
    CanonicalArray out := by
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
                        have hcan := decode_k_loop_success_canonical_fuel n.val self self.row
                          offset_values offset { start := 0#usize, «end» := n }
                          (Array.repeat n AspisR1DecodeKFullV10.aspis_core.field.QM31.ZERO)
                          loopOut none
                          (by rfl) (by
                            have hz : (0#usize).val = 0 := by scalar_tac
                            rw [hz]
                            omega)
                          zero_array_canonical hloop
                        exact hcan
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
#print axioms decode_k_success_canonical
end AspisR1DecodeKFullSuccessCanonicality
