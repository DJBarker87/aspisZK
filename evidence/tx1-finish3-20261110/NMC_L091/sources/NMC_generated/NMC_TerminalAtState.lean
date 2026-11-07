import NLC_ReadsReady
import NMC_ReachableOrigins
import NMC_TerminalSegment
import NLU_SameTerminal
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMC_Terminal
open Aeneas Aeneas.Std Result AspisR1PublicPreparation FIq_Carriers NMC_Parent
/-- Domain installation at the actual terminal parent slots. This uses the
same initial parser input and the provenance derived from the occurrence
fold; no successful child or independently selected array is a hypothesis. -/
theorem actual_arguments {H : Type} (native : NJM_RoundsCut.Observations)
 (cut : NJM_RoundsCut.Cut native) (token frame : Nat)
 (input : NLU.Input H) (domain : NLU.InputDomain input)
 (s : NLU.State H) (reached : NLU.Reachable input s) (atSite : s.machine.next=.terminal) :
 ∃ claims alpha,s.machine.locals.claims=some claims ∧ s.machine.locals.alpha=some alpha ∧
 (∀ row∈(mapArray (mapArray toQ) claims).val,FIw_ArrayValue.canonical row) ∧
 FIw_ArrayValue.canonical (mapArray toQ alpha) ∧
 NLU_Terminal.nativeTerminal input.publicValue claims alpha input.challenges=
 (IDa_Deployed.boundaries input.reservation).terminal input.publicValue claims alpha input.challenges := by
 have invariant:=NLU.reachable_invariant input s reached
 have initialized:=NLC_Finish.ready_reads s.machine invariant.1.1
 simp only [NLC_Finish.ReadsReady,atSite] at initialized
 obtain ⟨claims,claimsRead⟩:=NLC_Finish.initialized_read s.machine.locals.claims initialized.1
 obtain ⟨alpha,alphaRead⟩:=NLC_Finish.initialized_read s.machine.locals.alpha initialized.2
 have claimsStored : s.machine.locals.claims=some claims := by
  cases h : s.machine.locals.claims with
  | none=>rw [h] at claimsRead;cases claimsRead
  | some value=>rw [h] at claimsRead;cases Result.ok.inj claimsRead;rfl
 have alphaStored : s.machine.locals.alpha=some alpha := by
  cases h : s.machine.locals.alpha with
  | none=>rw [h] at alphaRead;cases alphaRead
  | some value=>rw [h] at alphaRead;cases Result.ok.inj alphaRead;rfl
 obtain ⟨bytes,pre,parsed,prefixEq⟩:=domain.parsedPrefix
 have origins:=NMC_Origins.reachable input s reached
 have claimsReturned:=origins.1 claims claimsStored
 obtain ⟨running,transcript,roundsReturned⟩:=origins.2 alpha alphaStored
 rw [invariant.2] at claimsReturned roundsReturned
 have hc:=NLU_Terminal.claims_domain input.reservation bytes pre parsed
 rw [←prefixEq,claimsReturned] at hc
 have ha:=NKQ_AlphaDomain.source native cut token frame input.digest bytes input.transcript
 rw [parsed] at ha
 dsimp only at ha
 have actualRound : (PreparedHashCode.run (S1SemanticCode.rounds NJM_RoundJoin.R input.digest input.prefix1 input.transcript)).2=
  ok (.Ok (running,alpha,transcript)) := by
  rw [PreparedHashCode.run_value];exact roundsReturned
 rw [←prefixEq,actualRound] at ha
 have na:=NLU_Terminal.array_to_native alpha ha
 exact ⟨claims,alpha,claimsStored,alphaStored,hc,na,
  NLU_Terminal.installed input.publicValue claims alpha input.challenges domain.terminal hc na⟩
#print axioms actual_arguments
set_option pp.proofs false in #print actual_arguments
end AspisR1.NMC_Terminal
end
