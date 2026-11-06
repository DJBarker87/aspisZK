import NLR_PrepareReachedDomain
import NHS_CallerWidths
import RPz7_F3M_InactiveCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLR_PrepareArgumentDomains
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
/-- Source-prefix producer facts on the SAME view. No constructor/scalar
success or opening packet is needed. Native087 still must realize this
reached prefix and its concrete installation. -/
theorem source (base : Ops) (reserved : Bool) (i : NLJ_Prepare.Input Unit)
 (v : verifier.View) (proofSize : i.proof.val.length=57607)
 (reached : NHL_PrepareModel.Reaches base reserved i.digest i.proof v) :
 let retained := InstalledPreparation.retainedView v
 retained.variant=.S2 ∧ retained.y1.val.length=928 ∧ retained.round0.val.length=224 ∧
 retained.round1.val.length=224 ∧ retained.final_message.val.length=2048 ∧
 NFN_LPi_FieldValues.canonE (NFW_SampledDomains.toNative retained.inactive) := by
 obtain ⟨variant,ySize,r0,r1,final⟩ := NHS_CallerWidths.reached base reserved i.digest i.proof v proofSize reached
 obtain ⟨_,_,semantic,y1,_,_,view,_⟩ := NHL_PrepareDomain.reached base reserved i.digest i.proof v proofSize reached
 have inactive := F3M_InactiveCanonical.source i.proof semantic y1 v view
 exact ⟨variant,ySize,r0,r1,final,NFW_SampledDomains.gamma_canonical _ inactive⟩
#print axioms source
set_option pp.proofs false
#print source
end AspisR1.NLR_PrepareArgumentDomains
end
