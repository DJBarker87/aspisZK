import Query31ModelScanCall
set_option autoImplicit false
namespace AspisR1.NBA_QueryTrace
open Aeneas Aeneas.Std Result ControlFlow
open Query31ExplicitListLoop Query31ExplicitScanBody
abbrev State := CurrentScan

/-- Source-order word trace. Each edge is ONE actual Std-instantiated source
body observation; no whole scan result or independently chosen final array. -/
inductive Trace : List U32 → State → State → Option Bool → Prop where
  | exhausted (s : State) : Trace [] s s (some false)
  | stopped (x : U32) (xs : List U32) (s : State)
      (full : s.accepted_len=22#usize ∨ s.draws=64#usize) : Trace (x::xs) s s none
  | continuing (x : U32) (xs : List U32) (s next final : State) (stop : Option Bool)
      (step : body (stdOps listNext) (x::xs) s=ok (.cont (xs,next)))
      (tail : Trace xs next final stop) : Trace (x::xs) s final stop

/-- Induction converts the native local-step sequence into the exact installed
scanner carrier, including stop-before-word and no-check-after-last-word. -/
theorem source {xs : List U32} {s final : State} {stop : Option Bool}
    (tr : Trace xs s final stop) : scanListLoop xs s=ok (final,stop) := by
  induction tr with
  | exhausted s =>
    unfold scanListLoop step
    rw [Aeneas.Std.loop.eq_def]
    simp only [body,stdOps,listNext,bind_tc_ok]
  | stopped x xs s full =>
    unfold scanListLoop step
    rw [Aeneas.Std.loop.eq_def]
    rcases full with hf | hc
    · simp only [body,stdOps,listNext,bind_tc_ok,hf,↓reduceIte]
    · by_cases hf : s.accepted_len=22#usize
      · simp only [body,stdOps,listNext,bind_tc_ok,hf,↓reduceIte]
      · simp only [body,stdOps,listNext,bind_tc_ok,hf,hc,↓reduceIte]
  | continuing x xs s next final stop step tail ih =>
    unfold scanListLoop step
    rw [Aeneas.Std.loop.eq_def]
    change (do let st ← body (stdOps listNext) (x::xs) s
               match st with
               | .done v => ok v
               | .cont v => Aeneas.Std.loop Query31ExplicitListLoop.step v)=_
    rw [step,bind_tc_ok]
    exact ih

theorem unique {xs : List U32} {s left right : State} {a b : Option Bool}
    (lt : Trace xs s left a) (rt : Trace xs s right b) : left=right ∧ a=b := by
  have h := Result.ok.inj ((source lt).symm.trans (source rt))
  exact ⟨congrArg Prod.fst h,congrArg Prod.snd h⟩

#print axioms source
#print axioms unique
end AspisR1.NBA_QueryTrace
