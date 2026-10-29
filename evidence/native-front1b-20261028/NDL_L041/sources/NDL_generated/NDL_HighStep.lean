import NCJ_ForwardRange
import NCJ_CellCanon
import LPm_PublicState
set_option autoImplicit false
noncomputable section
namespace NDL_HighStep
open Aeneas Aeneas.Std Result ControlFlow AspisR1 LPi_FieldValues
abbrev Iter := NCJ_ForwardRange.Range
abbrev Dot := FIo_Native.fast_pairing.EbyKDot

/-- Total Result/error/state association at the actual emitted loop body. -/
theorem cut (partials : Array NE 4#usize) (coeffs : Array NQ 4#usize)
    (iter rest : Iter) (s : Usize) (before after : Dot) (value : NE) (scalar : NQ)
    (r : core.result.Result Unit Unit)
    (next : NCJ_ForwardRange.next iter=ok (some s,rest))
    (readP : Array.index_usize partials s=ok value)
    (readQ : Array.index_usize coeffs s=ok scalar)
    (push : FIo_Native.fast_pairing.EbyKDot.push before value scalar=ok (r,after)) :
    FIo_Native.weights.high_dot_loop.body partials coeffs iter before =
      match r with
      | .Ok _ => ok (cont (rest,after))
      | .Err _ => ok (done (core.result.Result.Err FIo_Native.verifier.Error.Parse)) := by
  unfold NCJ_ForwardRange.next at next
  simp only [FIo_Native.weights.high_dot_loop.body,next,readP,readQ,push,bind_tc_ok]

/-- Canonical input arrays and the chronological count invariant CONSTRUCT
success on this SAME state and SAME selected inputs. -/
theorem active (partials : Array NE 4#usize) (coeffs : Array NQ 4#usize)
    (hp : ∀ x∈partials.val,canonE x) (hq : NCJ_CellCanon.array coeffs)
    (iter : Iter) (finish : iter.end.val=4) (more : iter.start.val<iter.end.val)
    (before : Dot) (count : before.count.val≤iter.start.val) :
    ∃ rest after,
      FIo_Native.weights.high_dot_loop.body partials coeffs iter before=ok (cont (rest,after)) ∧
      rest.start.val=iter.start.val+1 ∧ rest.end.val=4 ∧ after.count.val≤rest.start.val := by
  obtain ⟨rest,next,inc,last⟩ := NCJ_ForwardRange.active iter more
  have bound : iter.start.val<4 := by omega
  let p := NCJ_GuardExact.pick partials iter.start.val bound
  let q := NCJ_GuardExact.pick coeffs iter.start.val bound
  have readP := NCJ_GuardExact.index partials iter.start bound
  have readQ := NCJ_GuardExact.index coeffs iter.start bound
  change Array.index_usize partials iter.start=ok p at readP
  change Array.index_usize coeffs iter.start=ok q at readQ
  have cp : canonE p := by
    apply hp
    exact List.mem_of_getElem? (show partials.val[iter.start.val]?=some p by simp [p,NCJ_GuardExact.pick])
  have cq := NCJ_CellCanon.array_read coeffs iter.start q hq readQ
  obtain ⟨lo,hi,after,push,_,_,_,_,afterCount⟩ := LPm_PublicState.source before p q cp cq (by omega)
  refine ⟨rest,after,cut partials coeffs iter rest iter.start before after p q (.Ok ()) next readP readQ push,
    inc,?_,?_⟩
  · rw [last];exact finish
  · omega

#print axioms cut
#print axioms active
end NDL_HighStep
end
