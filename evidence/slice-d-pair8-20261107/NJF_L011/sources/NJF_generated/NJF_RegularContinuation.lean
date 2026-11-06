import NJF_SharedContinuation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJF_RegularContinuation
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_PairControl AspisR1Stage2
open NJF_RegularCut NJF_RegularInstantiation NJF_SharedContinuation
variable [FIo_Native.Allocation]

/-- Replacing the complete regular/shared oracle stage by its CLOSED child
results gives the parent's source continuation. Returning Err writes remain in
segment until the caller discards them; outer aborts have no suffix. -/
theorem interpreted (c : Context) (before : Scratch)
 (hf : NHI_TensorOuterStep.Factors c.w.value) :
 continueWith c (NJF_RegularInstantiation.segment c before).1=NIT_PairControl.regular c before := by
 unfold NIT_PairControl.regular
 rw [(NIT_ControlCuts.guard c.w.value).1]
 simp only [bind_tc_ok]
 change continueWith c (NJF_RegularInstantiation.segment c before).1=
  (regularReply c before >>= fun result=>afterRegular c (NGM_GuardExact.guard c.w.value 2#usize) result.2.2 result.1)
 cases hr : regularReply c before with
 | fail err => simp only [NJF_RegularInstantiation.segment,hr,continueWith];rfl
 | div => simp only [NJF_RegularInstantiation.segment,hr,continueWith];rfl
 | ok value =>
  rcases value with ⟨reply,scratch,parts⟩
  cases reply with
  | Err err => simp only [NJF_RegularInstantiation.segment,hr,continueWith,bind_tc_ok,afterRegular,afterHigh]
  | Ok unit =>
   cases unit
   cases hs : NGM_GuardExact.guard c.w.value 2#usize with
   | false => simp only [NJF_RegularInstantiation.segment,hr,hs,ite_false,continueWith,bind_tc_ok,afterRegular,afterHigh,Bool.false_eq_true]
   | true =>
    simp only [NJF_RegularInstantiation.segment,hr,hs,ite_true,bind_tc_ok,afterRegular]
    exact NJF_SharedContinuation.source c scratch parts hf

/-- Forward native-oracle instantiation into the already proved source capsule.
The child's complete Result is constructed, never supplied as a hypothesis. -/
theorem source (c : Context) (before : Scratch)
 (domain : NIT_PairDomain.Domain c.w.value c.alpha.value c.f.value c.kappa)
 (c0 : canonical c.ap0.value) (c1 : canonical c.ap1.value)
 (inv : NHX_RegularPost.Inv before initial) :
 continueWith c (G (NGM_GuardExact.guard c.w.value 2#usize) (instantiate c before)).1=
 (NIW_AlignRegularPhase.run c before).1 := by
 rw [NJF_RegularInstantiation.source]
 exact (interpreted c before domain.factors).trans (NIW_AlignRegularPhaseSource.source c before domain c0 c1 inv)

#print source
#print axioms interpreted
#print axioms source
end AspisR1.NJF_RegularContinuation
