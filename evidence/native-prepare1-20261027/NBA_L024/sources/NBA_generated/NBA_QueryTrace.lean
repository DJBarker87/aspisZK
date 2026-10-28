import Query31ModelScanCall
import NBA_QueryStep
set_option autoImplicit false
namespace AspisR1.NBA_QueryTrace
open Aeneas Aeneas.Std Result ControlFlow
open Query31ExplicitListLoop Query31ExplicitScanBody
abbrev State := Query31ExplicitScanBody.CurrentScan

/-- Source-order word trace. Each edge is ONE actual Std-instantiated source
body observation; no whole scan result or independently chosen final array. -/
inductive Trace : List U32 → State → State → Option Bool → Prop where
  | exhausted (s : State) : Trace [] s s (some false)
  | stopped (x : U32) (xs : List U32) (s : State)
      (full : s.accepted_len=22#usize ∨ s.draws=64#usize) : Trace (x::xs) s s none
  | continuing (x : U32) (xs : List U32) (s next final : State) (stop : Option Bool)
      (hlen : s.accepted_len.val<22) (hdraw : s.draws.val<64)
      (member : Bool) (membership : member=decide (x.val ∈ acceptedPrefix s))
      (frame : NBA_QueryStep.Frame s next x member)
      (tail : Trace xs next final stop) : Trace (x::xs) s final stop

/-- Induction converts the native local-step sequence into the exact installed
scanner carrier, including stop-before-word and no-check-after-last-word. -/
theorem source {xs : List U32} {s final : State} {stop : Option Bool}
    (tr : Trace xs s final stop) : scanListLoop xs s=ok (final,stop) := by
  induction tr with
  | exhausted s =>
    have edge : body (stdOps listNext) ([] : List U32) s=ok (.done (s,some false)) := by
      simp only [body,stdOps,listNext,bind_tc_ok]
      rfl
    unfold scanListLoop step
    rw [Aeneas.Std.loop.eq_def]
    dsimp! only
    rw [edge]
  | stopped x xs s full =>
    have edge : body (stdOps listNext) (x::xs) s=ok (.done (s,none)) := by
      rcases full with hf | hc
      · simp only [body,stdOps,listNext,bind_tc_ok,hf,↓reduceIte]
        rfl
      · by_cases hf : s.accepted_len=22#usize
        · simp only [body,stdOps,listNext,bind_tc_ok,hf,↓reduceIte]
          rfl
        · simp only [body,stdOps,listNext,bind_tc_ok,hf,hc,↓reduceIte]
          rfl
    unfold scanListLoop step
    rw [Aeneas.Std.loop.eq_def]
    dsimp! only
    rw [edge]
  | continuing x xs s next final stop hlen hdraw member membership frame tail ih =>
    have edge : body (stdOps listNext) (x::xs) s=ok (.cont (xs,next)) := by
      cases member with
      | false =>
        have hm : x.val ∉ acceptedPrefix s := by
          intro hm
          simp only [hm,decide_true] at membership
          cases membership
        exact NBA_QueryStep.fresh xs s next x hlen hdraw hm frame
      | true =>
        have hm : x.val ∈ acceptedPrefix s := by
          by_contra hn
          simp only [hn,decide_false] at membership
          cases membership
        exact NBA_QueryStep.duplicate xs s next x hlen hdraw hm frame
    unfold scanListLoop step
    rw [Aeneas.Std.loop.eq_def]
    dsimp! only
    rw [edge]
    exact ih

theorem unique {xs : List U32} {s left right : State} {a b : Option Bool}
    (lt : Trace xs s left a) (rt : Trace xs s right b) : left=right ∧ a=b := by
  have h := Result.ok.inj ((source lt).symm.trans (source rt))
  exact ⟨congrArg Prod.fst h,congrArg Prod.snd h⟩

#print axioms source
#print axioms unique
end AspisR1.NBA_QueryTrace
