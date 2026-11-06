import NIW_AlignRegularPhase
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignRegularPhaseSource
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_PairControl
variable [FIo_Native.Allocation]

theorem child (c : Context) (before : Scratch) :
 (NIW_AlignRegularPhase.run c before).2.outcome=
 FIo_Native.weights.process_regular_kinds c.w.value (NGM_GuardExact.guard c.w.value 2#usize)
  c.alpha.value.to_slice c.f.value 2#usize 64#usize c.ap0.value c.ap1.value before initial := by
 have source := NIW_AlignRegularExecution.source c.w.value
  (NGM_GuardExact.guard c.w.value 2#usize) c.alpha.value.to_slice c.f.value c.ap0.value c.ap1.value before initial
 cases result : (NIW_AlignRegularExecution.execute c.w.value c.alpha.value.to_slice c.f.value
  c.ap0.value c.ap1.value (NHM_RegularKinds.kinds (NGM_GuardExact.guard c.w.value 2#usize)) before initial).1 with
 | fail err => simp only [NIW_AlignRegularPhase.run,result];exact result.symm.trans source.symm
 | div => simp only [NIW_AlignRegularPhase.run,result];exact result.symm.trans source.symm
 | ok value =>
  rcases value with ⟨reply,after,parts⟩
  simp only [NIW_AlignRegularPhase.run,result]
  exact result.symm.trans source.symm

theorem events (c : Context) (before : Scratch) :
 (NIW_AlignRegularPhase.run c before).2.events=
 (NIW_AlignRegularExecution.execute c.w.value c.alpha.value.to_slice c.f.value
  c.ap0.value c.ap1.value (NHM_RegularKinds.kinds (NGM_GuardExact.guard c.w.value 2#usize)) before initial).2 := by
 cases result : (NIW_AlignRegularExecution.execute c.w.value c.alpha.value.to_slice c.f.value
  c.ap0.value c.ap1.value (NHM_RegularKinds.kinds (NGM_GuardExact.guard c.w.value 2#usize)) before initial).1 with
 | fail err => simp only [NIW_AlignRegularPhase.run,result]
 | div => simp only [NIW_AlignRegularPhase.run,result]
 | ok value => rcases value with ⟨reply,after,parts⟩;simp only [NIW_AlignRegularPhase.run,result]

theorem source (c : Context) (before : Scratch)
 (domain : NIT_PairDomain.Domain c.w.value c.alpha.value c.f.value c.kappa)
 (c0 : canonical c.ap0.value) (c1 : canonical c.ap1.value)
 (inv : NHX_RegularPost.Inv before initial) :
 NIT_PairControl.regular c before=(NIW_AlignRegularPhase.run c before).1 :=
 NIT_RegularChain.interpreted c before _ domain (NIW_AlignRegularPhase.trace c before domain c0 c1 inv)

theorem frames (c : Context) (before : Scratch)
 (domain : NIT_PairDomain.Domain c.w.value c.alpha.value c.f.value c.kappa)
 (c0 : canonical c.ap0.value) (c1 : canonical c.ap1.value)
 (inv : NHX_RegularPost.Inv before initial) :
 ∀ event∈(NIW_AlignRegularPhase.run c before).2.events,NIW_AlignRegularFrames.Frame event := by
 rw [events]
 exact NIW_AlignRegularFrames.all c.w.value c.alpha.value.to_slice c.f.value c.ap0.value c.ap1.value
  domain.s2 domain.factors c0 c1 _
  (fun k hk=>NHM_RegularDomain.membership (NGM_GuardExact.guard c.w.value 2#usize) k hk) before initial inv

#print axioms child
#print axioms events
#print axioms source
#print axioms frames
end AspisR1.NIW_AlignRegularPhaseSource
