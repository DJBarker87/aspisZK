import NMO_PrefixErrors
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMO_ErrorFrontier
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
open PreparedHashCode (Code Log run)
/-- Terminal Err maps to Public with no downstream arithmetic or digest
suffix. This is a branch lemma, not a child-result premise of a row root. -/
theorem terminal_error {H : Type} (i : Input H) (running : Q) (alpha : Alpha)
 (transcript : r1_wire.SemanticTranscript H) (claims : Claims)
 (error : aspis_core.state_only_prefix.r0.Error)
 (entered : (IDa_Deployed.boundaries i.reservation).terminal i.publicValue claims alpha i.challenges=ok (.Err error)) :
 run (NLI_Source.suffix_terminal i running alpha transcript claims)=([],ok (.Err r1_wire.Error.Public)) := by
 unfold NLI_Source.suffix_terminal
 rw [entered]
 rfl
/-- The major-occurrence frontier stops at mapPublic: no mask or arithmetic
occurrence enters this source invocation. Abort heap/cleanup is not invented. -/
theorem terminal_steps {H : Type} (s : NLC_Finish.State H) (claims : Claims) (alpha : Alpha)
 (atSite : s.next=.terminal) (hc : s.locals.claims=some claims) (ha : s.locals.alpha=some alpha)
 (error : aspis_core.state_only_prefix.r0.Error)
 (entered : (IDa_Deployed.boundaries s.input.reservation).terminal s.input.publicValue claims alpha s.input.challenges=ok (.Err error)) :
 ∃ after,run (NLC_Finish.step s)=([],ok (.inr after)) ∧
 run (NLC_Finish.step after)=([],ok (.inl (.Err r1_wire.Error.Public))) ∧
 Invocation 2 s (ok (.Err r1_wire.Error.Public)) [] [.terminal,.mapPublic] := by
 let after:=NLC_Finish.put s .mapPublic {s.locals with claims:=some claims,alpha:=some alpha,terminalReply:=some (.Err error)}
 have first : run (NLC_Finish.step s)=([],ok (.inr after)) := by
  dsimp only [after]
  simp only [NLC_Finish.step,atSite,hc,ha]
  change run (PreparedHashCode.Code.step
    ((IDa_Deployed.boundaries s.input.reservation).terminal s.input.publicValue claims alpha s.input.challenges)
    (fun result=>PreparedHashCode.Code.done (Sum.inr (NLC_Finish.put s .mapPublic
      {s.locals with claims:=some claims,alpha:=some alpha,terminalReply:=some result}) : Post H))) = _
  rw [entered]
  rfl
 have second : run (NLC_Finish.step after)=([],ok (.inl (.Err r1_wire.Error.Public))) := by
  rfl
 refine ⟨after,first,second,?_⟩
 have trace:=Invocation.next first (Invocation.returned (n:=0) second)
 simpa only [atSite,after,NLC_Finish.put,List.nil_append,Nat.zero_add] using trace
#print axioms terminal_error
#print axioms terminal_steps
set_option pp.proofs false in #print terminal_steps
end AspisR1.NMO_ErrorFrontier
end
