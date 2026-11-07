import NMO_Transcription
import NLI_SourceEquality
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMO_PrefixErrors
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
open PreparedHashCode (Code Log run)
/-- Branch lemma only: the observed child prefix is retained, with no suffix
queries after the first returned Error. The branch equality is NOT a root
hypothesis; a full row must discharge it by the CLOSED child packet. -/
theorem rounds_error {H : Type} (i : Input H) (log : Log) (error : r1_wire.Error)
 (entered : run (S1SemanticCode.rounds NJM_RoundJoin.R i.digest i.prefix1 i.transcript)=
 (log,ok (.Err error))) :
 run (S1SemanticCode.finish NJM_RoundJoin.R (IDa_Deployed.boundaries i.reservation)
 i.digest i.publicValue i.prefix1 i.transcript i.challenges none)=(log,ok (.Err error)) := by
 rw [← NLI_Source.suffix_eq_finish]
 unfold NLI_Source.suffix_rounds
 change run (PreparedHashCode.bind _ _) = _
 rw [AuS1_Trace.run_bind,entered]
 simp only [AuS1_Trace.continueRun]
 change (log ++ [],_) = _
 rw [List.append_nil]
 rfl
/-- A child's outer abort preserves its attempted digest history and admits
no invented parent suffix, post-abort heap or cleanup. -/
theorem rounds_abort {H : Type} (i : Input H) (log : Log) (error : Error)
 (entered : run (S1SemanticCode.rounds NJM_RoundJoin.R i.digest i.prefix1 i.transcript)=
 (log,fail error)) :
 run (S1SemanticCode.finish NJM_RoundJoin.R (IDa_Deployed.boundaries i.reservation)
 i.digest i.publicValue i.prefix1 i.transcript i.challenges none)=(log,fail error) := by
 rw [← NLI_Source.suffix_eq_finish]
 unfold NLI_Source.suffix_rounds
 change run (PreparedHashCode.bind _ _) = _
 rw [AuS1_Trace.run_bind,entered]
 rfl
/-- Claims errors stop before challenge-copy/terminal, for arbitrary already
returned rounds values. This is a source branch lemma, not a native root. -/
theorem claims_error {H : Type} (i : Input H) (running : Q) (alpha : Alpha)
 (transcript : r1_wire.SemanticTranscript H) (error : r1_wire.Error)
 (entered : (IDa_Deployed.boundaries i.reservation).claims i.prefix1=ok (.Err error)) :
 run (NLI_Source.suffix_claims i running alpha transcript)=([],ok (.Err error)) := by
 unfold NLI_Source.suffix_claims
 rw [entered]
 rfl
#print axioms rounds_error
#print axioms rounds_abort
#print axioms claims_error
set_option pp.proofs false in #print rounds_error
set_option pp.proofs false in #print claims_error
end AspisR1.NMO_PrefixErrors
end
