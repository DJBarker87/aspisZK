import NIW_AlignRegularFrames
import NIW_AlignAfterPhase
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignRegularPhase
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_PairControl
variable [FIo_Native.Allocation]

structure Log where
 outcome : Result NHM_RegularKinds.Reply
 events : List NIW_AlignRegularStream.Event
 tail : Option NIW_AlignAfterPhase.Log

def run (c : Context) (before : Scratch) : Result NR × Log :=
 let shared := NGM_GuardExact.guard c.w.value 2#usize
 let observed := NIW_AlignRegularExecution.execute c.w.value c.alpha.value.to_slice c.f.value
  c.ap0.value c.ap1.value (NHM_RegularKinds.kinds shared) before initial
 match observed.1 with
 | fail err => (fail err,⟨observed.1,observed.2,none⟩)
 | div => (div,⟨observed.1,observed.2,none⟩)
 | ok (reply,after,parts) =>
  let tail := NIW_AlignAfterPhase.run c shared parts reply
  (tail.1,⟨observed.1,observed.2,some tail.2⟩)

theorem trace (c : Context) (before : Scratch)
 (domain : NIT_PairDomain.Domain c.w.value c.alpha.value c.f.value c.kappa)
 (c0 : canonical c.ap0.value) (c1 : canonical c.ap1.value)
 (inv : NHX_RegularPost.Inv before initial) :
 NIT_RegularChain.Trace c before (run c before).1 := by
 have source := NIW_AlignRegularExecution.source c.w.value
  (NGM_GuardExact.guard c.w.value 2#usize) c.alpha.value.to_slice c.f.value c.ap0.value c.ap1.value before initial
 cases result : (NIW_AlignRegularExecution.execute c.w.value c.alpha.value.to_slice c.f.value
  c.ap0.value c.ap1.value (NHM_RegularKinds.kinds (NGM_GuardExact.guard c.w.value 2#usize)) before initial).1 with
 | fail err =>
  have call := source.trans result
  simp only [run,result]
  exact .failed err call
 | div =>
  have call := source.trans result
  simp only [run,result]
  exact .diverged call
 | ok value =>
  rcases value with ⟨reply,after,parts⟩
  have call := source.trans result
  have post := NIG_PairFrames.regular c.w.value _ c.alpha.value.to_slice c.f.value c.ap0.value c.ap1.value
   domain.s2 domain.factors c0 c1 before after initial parts reply inv call
  simp only [run,result]
  exact .returned reply after parts _ call
   (NIW_AlignAfterPhase.trace c _ parts reply domain c0 c1 post.2.2)

#print axioms trace
end AspisR1.NIW_AlignRegularPhase
