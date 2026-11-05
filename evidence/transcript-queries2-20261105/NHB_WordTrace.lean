import NHB_Association
set_option autoImplicit false
namespace AspisR1.NHB_WordTrace
open Aeneas Aeneas.Std Result
open Query31ExplicitListLoop Query31ExplicitScanBody
abbrev State := NGQ_SamplerTrace.State

/-- Iterator next occurs before stop testing. The stopped edge therefore
consumes its candidate while preserving the entire scan state. -/
inductive Trace : Nat → List U32 → State → State → Nat → Option Bool → Prop where
 | exhausted (cursor : Nat) (s : State) : Trace cursor [] s s cursor (some false)
 | stopped (cursor : Nat) (x : U32) (xs : List U32) (s : State)
     (full : s.accepted_len=22#usize ∨ s.draws=64#usize) :
     Trace cursor (x::xs) s s (cursor+1) none
 | continuing (cursor : Nat) (x : U32) (xs : List U32) (s next final : State)
     (last : Nat) (stop : Option Bool)
     (hlen : s.accepted_len.val<22) (hdraw : s.draws.val<64)
     (frame : NGQ_SamplerStep.Frame s next x
       (NHB_Membership.reference x (s.accepted.val.take s.accepted_len.val)))
     (tail : Trace (cursor+1) xs next final last stop) :
     Trace cursor (x::xs) s final last stop

/-- Rule-B induction. Native producer must supply these local edges on the SAME
word iterator; this theorem neither invents nor separately chooses an output. -/
theorem association {cursor last : Nat} {xs : List U32} {s final : State}
    {stop : Option Bool} (trace : Trace cursor xs s final last stop) :
    NGQ_SamplerTrace.Trace xs s final stop := by
  induction trace with
  | exhausted cursor s => exact .exhausted s
  | stopped cursor x xs s full => exact .stopped x xs s full
  | continuing cursor x xs s next final last stop hlen hdraw frame tail ih =>
    rw [NHB_Membership.prefix_membership] at frame
    exact .continuing x xs s next final stop hlen hdraw
      (decide (x.val ∈ acceptedPrefix s)) rfl frame ih

theorem cursor_bound {cursor last : Nat} {xs : List U32} {s final : State}
    {stop : Option Bool} (trace : Trace cursor xs s final last stop) :
    cursor≤last ∧ last≤cursor+xs.length := by
  induction trace with
  | exhausted cursor s => simp only [List.length_nil,Nat.add_zero]; omega
  | stopped cursor x xs s full => simp only [List.length_cons]; omega
  | continuing cursor x xs s next final last stop hlen hdraw frame tail ih =>
    simp only [List.length_cons]
    omega

/-- Complete installed list-loop Result at the observed final state. -/
theorem source {cursor last : Nat} {xs : List U32} {s final : State}
    {stop : Option Bool} (trace : Trace cursor xs s final last stop) :
    scanListLoop xs s=ok (final,stop) :=
  NGQ_SamplerTrace.source (association trace)

#print axioms association
#print axioms cursor_bound
#print axioms source
end AspisR1.NHB_WordTrace
