import NMO_ArrayReachable
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMO_MaskAtState
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
/-- Every own-argument clause of mask076 is derived at its actual source
slots, including all cells of both temporary arrays and the actual alpha. -/
theorem arguments {H : Type} (native : NJM_RoundsCut.Observations)
 (cut : NJM_RoundsCut.Cut native) (token frame : Nat)
 (input : NLU.Input H) (domain : NLU.InputDomain input)
 (s : NLU.State H) (reached : NLU.Reachable input s) (atSite : s.machine.next=.mask) :
 ∃ low high blind alpha,s.machine.locals.low=some low ∧ s.machine.locals.high=some high ∧
 s.machine.locals.blind=some blind ∧ s.machine.locals.alpha=some alpha ∧
 (∀ q∈low.val,NKQ_MaskCuts.Canon q) ∧ (∀ q∈high.val,NKQ_MaskCuts.Canon q) ∧
 NKQ_MaskCuts.Canon blind ∧ NKQ_MaskCuts.CanonAlpha alpha := by
 have initialized:=NLC_Finish.ready_reads s.machine (NLU.reachable_invariant input s reached).1.1
 simp only [ReadsReady,atSite] at initialized
 obtain ⟨low,lo⟩:=NMC_Records.some_slot s.machine.locals.low initialized.1
 obtain ⟨high,hi⟩:=NMC_Records.some_slot s.machine.locals.high initialized.2.1
 obtain ⟨blind,bl⟩:=NMC_Records.some_slot s.machine.locals.blind initialized.2.2.1
 obtain ⟨alpha,al⟩:=NMC_Records.some_slot s.machine.locals.alpha initialized.2.2.2
 have arrays:=NMO_ArrayStored.reachable input domain s reached
 exact ⟨low,high,blind,alpha,lo,hi,bl,al,arrays.1 low lo,arrays.2.1 high hi,arrays.2.2 blind bl,
 NMO_ClaimsAtState.alpha native cut token frame input domain s reached alpha al⟩
#print axioms arguments
set_option pp.proofs false in #print arguments
end AspisR1.NMO_MaskAtState
end
