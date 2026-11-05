import NIW_AlignFinishInvocation
import NIT_PairDomain
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignFinishDomains
open Aeneas Aeneas.Std Result NIT_Cuts AspisR1Stage2 NIW_AlignFinishExecution NIW_AlignFinishInvocation

def Inputs (p : verifier.Prepared) (v : verifier.View) (a : verifier.Accumulator) : Event → Prop
 | .round _ bytes alpha _ _ => bytes.val.length=224 ∧ LPi_FieldValues.canonE (FIo_Install.toE alpha)
 | .new prepared _ => prepared=p
 | .pair owner alpha message kappa _ => alpha=p.alpha.to_slice ∧ message=v.final_message ∧
   kappa=p.kappa ∧ NIT_PairDomain.Domain (FIo_Install.toWeights owner)
    (NIT_PairDomain.alpha p) message (FIo_Install.toE kappa)
 | .dot message weights _ => message=v.final_message ∧ weights=NHQ_WeightPort.weights a.weights.deref ∧
   weights.val.length=64

/-- All entered child domains come from this caller and the SAME actual NEW
return. The internal NEW return equation comes from case analysis on observe;
there is no successful-NEW hypothesis of this theorem. -/
theorem all (r : NP6_StdModel.Reservation) (proof : Slice U8)
 (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator)
 (domain : NIG_FinishInput.Domain proof v p a) :
 ∀ event∈(run r v p a).2,Inputs p v a event := by
 unfold run
 apply observe_all
 · exact ⟨domain.round0_words.1,(NIG_FinishAlpha.selected proof v p a domain 0#usize (by decide)).2⟩
 intro first firstCall
 apply observe_all
 · exact ⟨domain.round1_words.1,(NIG_FinishAlpha.selected proof v p a domain 1#usize (by decide)).2⟩
 intro claim claimCall
 apply observe_all
 · rfl
 intro owner newCall
 rw [NIG_PairInputs.alpha_prefix]
 apply observe_all
 · exact ⟨rfl,rfl,rfl,NIT_PairDomain.caller r proof v p a domain owner newCall⟩
 intro pair pairCall
 split
 · intro event member;cases member
 · apply observe_all
   · refine ⟨rfl,rfl,?_⟩
     exact (NHQ_WeightPort.width a.weights.deref).trans domain.accumulator.width
   intro actual dotCall event member
   cases member

#print axioms all
end AspisR1.NIW_AlignFinishDomains
