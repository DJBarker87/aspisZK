import NIW_AlignRegularPhaseSource
import NHX_RegularFrame
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignRegularPostBoundary
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_PairControl
variable [FIo_Native.Allocation]

def Post (c : Context) (before : Scratch) (outcome : Result NHM_RegularKinds.Reply) : Prop :=
 match outcome with
 | fail _ => True
 | div => True
 | ok (_,after,parts) => NHX_RegularPost.Inv after parts ∧
   ∀ j,(∀ k∈NHM_RegularKinds.kinds (NGM_GuardExact.guard c.w.value 2#usize),j≠k.val) →
    parts.val[j]?=initial.val[j]?

/-- Full regular post and omitted-kind frame on the actual observed complete
source reply, including returning Err writes. PairEdges.regular_post is never
identified with this value. No child-result clause is a hypothesis. -/
theorem source (c : Context) (before : Scratch)
 (domain : NIT_PairDomain.Domain c.w.value c.alpha.value c.f.value c.kappa)
 (c0 : canonical c.ap0.value) (c1 : canonical c.ap1.value)
 (inv : NHX_RegularPost.Inv before initial) :
 Post c before (NIW_AlignRegularPhase.run c before).2.outcome := by
 have observed := (NIW_AlignRegularPhaseSource.child c before).symm
 cases result : (NIW_AlignRegularPhase.run c before).2.outcome with
 | fail err => trivial
 | div => trivial
 | ok value =>
  rcases value with ⟨reply,after,parts⟩
  have call := observed.trans result
  refine ⟨NIG_PairFrames.regular c.w.value _ c.alpha.value.to_slice c.f.value c.ap0.value c.ap1.value
   domain.s2 domain.factors c0 c1 before after initial parts reply inv call,?_⟩
  intro j outside
  exact NHX_RegularFrame.source c.w.value _ c.alpha.value.to_slice c.f.value c.ap0.value c.ap1.value
   domain.s2 domain.factors c0 c1 before after initial parts reply inv j outside call

#print axioms source
end AspisR1.NIW_AlignRegularPostBoundary
