import NMO_MapStored
import NLU_FieldValues
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMO_MulAtState
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
/-- The multiplication domain is derived at the stored actual terminal slot.
No independent terminal value, child success or canonicality is a root premise. -/
theorem operands {H : Type} (native : NJM_RoundsCut.Observations)
 (cut : NJM_RoundsCut.Cut native) (token frame : Nat)
 (input : NLU.Input H) (domain : NLU.InputDomain input)
 (s : NLU.State H) (reached : NLU.Reachable input s) (atSite : s.machine.next=.multiply) :
 ∃ terminal,s.machine.locals.terminal=some terminal ∧
 JFv_RoundArithmetic.Canonical input.challenges.eta ∧
 JFv_RoundArithmetic.Canonical terminal := by
 have initialized:=NLC_Finish.ready_reads s.machine (NLU.reachable_invariant input s reached).1.1
 simp only [ReadsReady,atSite] at initialized
 have canonical:=(NMO_TerminalStored.reachable native cut token frame input domain s reached).2
 cases slot : s.machine.locals.terminal with
 | none=>rw [slot] at initialized;cases initialized
 | some terminal=>exact ⟨terminal,slot,domain.eta,canonical terminal slot⟩
/-- The emitted multiplication value law supplies the result and canonicality
on exactly those internally established operands; Kani never multiplies. -/
theorem product {H : Type} (native : NJM_RoundsCut.Observations)
 (cut : NJM_RoundsCut.Cut native) (token frame : Nat)
 (input : NLU.Input H) (domain : NLU.InputDomain input)
 (s : NLU.State H) (reached : NLU.Reachable input s) (atSite : s.machine.next=.multiply) :
 ∃ terminal value,s.machine.locals.terminal=some terminal ∧
 (IDa_Deployed.boundaries input.reservation).mul input.challenges.eta terminal=ok value ∧
 JFv_RoundArithmetic.Canonical value := by
 obtain ⟨terminal,stored,he,ht⟩:=operands native cut token frame input domain s reached atSite
 obtain ⟨value,returned,hv,_⟩:=NLU_FieldValues.mul_value input.reservation input.challenges.eta terminal he ht
 exact ⟨terminal,value,stored,returned,hv⟩
#print axioms operands
#print axioms product
set_option pp.proofs false in #print operands
set_option pp.proofs false in #print product
end AspisR1.NMO_MulAtState
end
