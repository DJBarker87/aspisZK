import HeapFilledOverwriteCandidateLoopCountV1
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
open AspisR1HeapFilledOverwrite
open HeapFilledOverwriteLoopV1 HeapFilledOverwriteLoopCountV1

namespace HeapFilledOverwriteCandidateSuccessTraceV1

theorem filled_success_trace {T : Type} (copyInst : core.marker.Copy T)
    (n : Std.Usize) (value : T) (out : alloc.vec.Vec T)
    (h : aspis_core.r0.heap.filled_overwrite copyInst n value = .ok (.Ok out)) :
    ∃ resized : alloc.vec.Vec T,
      aspis_core.r0.heap.filled_overwrite_loop { start := 0#usize, «end» := n }
        value resized = .ok out ∧
      SuccessfulTrace (body value) ({ start := 0#usize, «end» := n }, resized)
        n.val out := by
  unfold aspis_core.r0.heap.filled at h
  cases htry : alloc.vec.Vec.try_reserve_exact Global (alloc.vec.Vec.new T) n with
  | fail e => simp [htry] at h
  | div => simp [htry] at h
  | ok pair =>
    rcases pair with ⟨reserve, base⟩
    cases reserve with
    | Err err =>
      simp [htry, core.result.Result.map_err,
        core.result.Result.Insts.CoreOpsTry.branch,
        aspis_core.r0.heap.filled.closure.Insts.CoreOpsFunctionFnOnceTupleTryReserveErrorError.call_once,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from] at h
    | Ok token =>
      simp only [htry, core.result.Result.map_err, bind_tc_ok,
        core.result.Result.Insts.CoreOpsTry.branch] at h
      change (do
        let resized ← alloc.vec.Vec.resize copyInst.cloneInst base n value
        let filled ← aspis_core.r0.heap.filled_overwrite_loop
          { start := 0#usize, «end» := n } value resized
        ok (core.result.Result.Ok filled)) = .ok (.Ok out) at h
      cases hresize : alloc.vec.Vec.resize copyInst.cloneInst base n value with
      | fail e => simp [hresize] at h
      | div => simp [hresize] at h
      | ok resized =>
        simp only [hresize, bind_tc_ok] at h
        cases hloop : aspis_core.r0.heap.filled_overwrite_loop
            { start := 0#usize, «end» := n } value resized with
        | fail e => simp [hloop] at h
        | div => simp [hloop] at h
        | ok filled =>
          simp only [hloop, bind_tc_ok] at h
          injection h with hres
          injection hres with hout
          subst out
          exact ⟨resized, hloop,
            candidate_writes_exactly_n value resized filled n hloop⟩

#print axioms filled_success_trace
end HeapFilledOverwriteCandidateSuccessTraceV1
