import NHB_Membership
set_option autoImplicit false
namespace AspisR1.NHB_Association
open Aeneas Aeneas.Std Result ControlFlow
open Query31ExplicitListLoop Query31ExplicitScanBody

/-- Local native membership/caller frame are composed on the SAME scan state.
The reference predicate is over its actual active prefix, never a free Bool. -/
theorem continuing (xs : List U32) (s next : NGQ_SamplerTrace.State) (x : U32)
    (hlen : s.accepted_len.val < 22) (hdraw : s.draws.val < 64)
    (frame : NGQ_SamplerStep.Frame s next x
      (NHB_Membership.reference x (s.accepted.val.take s.accepted_len.val))) :
    body (stdOps listNext) (x::xs) s=ok (.cont (xs,next)) := by
  rw [NHB_Membership.prefix_membership] at frame
  by_cases member : x.val ∈ acceptedPrefix s
  · simp only [member,decide_true] at frame
    exact NGQ_SamplerStep.duplicate xs s next x hlen hdraw member frame
  · simp only [member,decide_false] at frame
    exact NGQ_SamplerStep.fresh xs s next x hlen hdraw member frame

#print axioms continuing
end AspisR1.NHB_Association
