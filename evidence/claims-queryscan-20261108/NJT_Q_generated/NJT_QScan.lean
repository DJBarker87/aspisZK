import NJT_QLeaves
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJT_QScan
open Aeneas Aeneas.Std Result NJT_QBase
open Query31ExplicitListLoop Query31ExplicitScanBody

structure WordPost where
 state : State
 stop : Bool

/-- Native observations of one arbitrary-prestate frozen word iteration, with
its real membership child supplied at the SAME prefix and candidate. This is
an observation family, not a replacement operation dictionary for the cohort. -/
abbrev Native := State → U32 → Bool → WordPost

/-- Reviewed K034/035 poststate projection. The scalar/window assertion is
NHK_word_ref and the complete membership log pins count, prefix, candidate and
post-increment draw. All22 windows are selected on the SAME pre/post state.
The native membership row is installed internally by run, never hypothesized. -/
def Cut (native : Native) : Prop :=
 ∀ (s : State) (x : U32) (reply : Bool), validState s → ∀ j : Fin 22,
  NHB_Observation.observe (native s x reply).state x 1 (native s x reply).stop j =
   NHK_WordAssociation.G s x 0 reply j

def run (native : Native) : List U32 → State → State × Option Bool
 | [],s => (s,some false)
 | x::xs,s =>
  let post:=native s x (NHB_Membership.reference x (s.accepted.val.take s.accepted_len.val))
  if post.stop then (post.state,none) else run native xs post.state

/-- Forward (y)(3) instantiation: choose each certified membership reply at the
actual prefix, then propagate the native step to the emitted list body. No
inverse raw-log or endpoint premise is used. -/
theorem trace (native : Native) (cut : Cut native)
 {xs : List U32} {s final : State} {stop : Option Bool}
 (edges : NGQ_SamplerTrace.Trace xs s final stop) (valid : validState s) :
 run native xs s=(final,stop) := by
 induction edges with
 | exhausted s => rfl
 | stopped x xs s full =>
  have hf : s.accepted_len.val=22 ∨ s.draws.val=64 := by
   rcases full with h|h
   · exact Or.inl (congrArg UScalar.val h)
   · exact Or.inr (congrArg UScalar.val h)
  let reply:=NHB_Membership.reference x (s.accepted.val.take s.accepted_len.val)
  have h:=NHK_WordAssociation.stopped_post s (native s x reply).state x 0 1
   (native s x reply).stop reply hf (cut s x reply valid)
  dsimp only [reply] at h
  simp only [run,h.1,if_true,h.2.2]
 | continuing x xs s next final stop hlen hdraw member membership frame tail ih =>
  have hm : member=NHB_Membership.reference x (s.accepted.val.take s.accepted_len.val) :=
   membership.trans (NHB_Membership.prefix_membership x s).symm
  rw [hm] at frame
  let reply:=NHB_Membership.reference x (s.accepted.val.take s.accepted_len.val)
  have h:=NHK_WordAssociation.logged_post s (native s x reply).state next x 0 1
   (native s x reply).stop reply hlen hdraw rfl (cut s x reply valid) frame
  have vn:=NGQ_SamplerStep.valid hlen hdraw frame
  dsimp only [reply] at h
  simp only [run,h.1,if_false,h.2.2]
  exact ih vn

/-- Complete source Result over arbitrary bounded prestate. The cut is the
reviewed one-iteration native certificate; all membership equations are
instantiated at their actual arguments inside the proof. -/
theorem source (native : Native) (cut : Cut native) (xs : List U32)
 (s : State) (valid : validState s) :
 scanListLoop xs s=ok (run native xs s) := by
 obtain ⟨final,pending,edges,good⟩:=NGQ_SamplerConstruct.construct xs s valid
 rw [trace native cut edges valid]
 exact NGQ_SamplerTrace.source edges

/-- Before-word stopping and the no-check-after-final-word convention remain
exactly those of the emitted scanListLoop, including its Option Bool marker. -/
theorem scan (native : Native) (cut : Cut native) (s : State)
 (valid : validState s) (b : Bytes) :
 Query31ModelScanCall.modelScanFn Query31ConcreteWordsDriverChain.actualQueryWords s b=
  ok (optionStop (run native (words b).val s).2,(run native (words b).val s).1) := by
 simp only [Query31ModelScanCall.modelScanFn,words_source,bind_tc_ok,source native cut _ s valid]

#print axioms trace
#print axioms source
#print axioms scan
#check @scan
end AspisR1.NJT_QScan
end
