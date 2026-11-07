import NLR_PrepareArgumentDomains
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMG_179_Widths
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
/-- SAME reached view; no constructor-success hypothesis. Source support only. -/
theorem source (base : Ops) (reserved : Bool) (i : NLJ_Prepare.Input Unit)
 (v : verifier.View) (proofSize : i.proof.val.length=57607)
 (reached : NHL_PrepareModel.Reaches base reserved i.digest i.proof v) :
 let retained := InstalledPreparation.retainedView v
 retained.variant=.S2 ∧ retained.y1.val.length=928 ∧ retained.round0.val.length=224 ∧
 retained.round1.val.length=224 ∧ retained.final_message.val.length=2048 ∧
 NFN_LPi_FieldValues.canonE (NFW_SampledDomains.toNative retained.inactive) :=
 NLR_PrepareArgumentDomains.source base reserved i v proofSize reached
#print axioms source
end AspisR1.NMG_179_Widths
end
