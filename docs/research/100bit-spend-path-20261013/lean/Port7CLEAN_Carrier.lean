import Port6AUTH_WordStability
import OraclePortRowsCanonicalC6
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port7CLEAN_Carrier
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open OraclePortStoredExperimentC4 OraclePortStoredAdmissionC4 OraclePortRuntimeBindingC7
open Port1_StoredCarrier Port6AUTH_SourceCut Port6AUTH_Prefix
theorem transcript_statement (D : LiteralByteProtocol.Decoder) (H : Bytes → State)
    (pub : LiteralTranscript.Public) (pf : LiteralProtocol.Proof) (n : Nat) :
    ((LiteralByteProtocol.protocol D).transcript H pub pf n).statement=pub := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

attribute [local irreducible] LiteralByteProtocol.protocol FS2.Protocol.transcript
  OraclePortStoredDecisionDraftC4.typedRows BinCompiledRunWordStability.wordsFromRun
  originalWith canon lift source


theorem erased_statement (pr : LiteralTranscript.Prefix) :
    (LiteralTranscript.erasePrefix pr).statement=pr.statement := rfl

theorem reached_statement (D : LiteralByteProtocol.Decoder) (H : Bytes → State)
    (pub : LiteralTranscript.Public) (pf : LiteralProtocol.Proof) :
    (Port6AUTH_Frames.reached D H pub pf).statement=pub :=
  (erased_statement _).trans (transcript_statement D H pub pf 33)


theorem parsed_valid (p : OraclePortCompactDraft.Parsed) (row : Nat) (bound : row<33) :
    LiteralTranscript.valid row (parsedProof p row) := by
  by_cases h0 : row=0
  · subst row; simp [parsedProof,LiteralTranscript.valid]
  · by_cases h2 : row=2
    · subst row; simp [parsedProof,LiteralTranscript.valid]
    · by_cases h30 : row=30
      · subst row; simp [parsedProof,LiteralTranscript.valid]
      · simp [parsedProof,h0,h2,h30,LiteralTranscript.valid,bound]

theorem canon_parsed (p : OraclePortCompactDraft.Parsed) :
    R16CanonReduction.proof (parsedProof p) = parsedProof p := by
  funext row
  by_cases h0 : row=0 <;> by_cases h2 : row=2 <;> by_cases h30 : row=30 <;>
    simp [R16CanonReduction.proof,R16CanonReduction.message,parsedProof,h0,h2,h30]

/-- Successful parsing of the ACTUAL first record's stored bytes determines
its canonical proof. A free stored argument would not suffice. -/
theorem first_proof (rust : Verifier) (P : ByteProver) (H : Bytes → State)
    (p : OraclePortCompactDraft.Parsed)
    (parsed : OraclePortCompactDraft.parse (first rust P H).2.1.stored=some p) :
    (first rust P H).2.1.proof=parsedProof p := by
  have actual : (first rust P H).2.1=canonInput (input (eval H P).2) := by
    simp only [first,OraclePortFrozen2Join.originalWith_eval,canon_eval,lift_eval]
  rw [actual] at parsed ⊢
  change OraclePortCompactDraft.parse (eval H P).2.stored=some p at parsed
  change R16CanonReduction.proof (proof (eval H P).2.stored)=_
  rw [proof,parsed,canon_parsed]

/-- Both annotation passes are connected to the SAME actual stored proof,
including the constructor schedule. No acceptance equivalence is assumed. -/
theorem rows (D : LiteralByteProtocol.Decoder) (rust : Verifier) (P : ByteProver)
    (H : Bytes → State) (p : OraclePortCompactDraft.Parsed) (q : Fin 22 → Fin 262144)
    (parsed : OraclePortCompactDraft.parse (first rust P H).2.1.stored=some p) :
    OraclePortReaderPlumbingC6.reword (build D (view (first rust P H)))
      (OraclePortStoredDecisionDraftC4.typedRows p q
        (Port6AUTH_Frames.reached D H (first rust P H).2.1.statement (first rust P H).2.1.proof)) =
      ((LiteralByteProtocol.protocol D).transcript H
        (eval H (source D rust P)).2.1.1 (eval H (source D rust P)).2.1.2 33).rounds := by
  let before := first rust P H
  let transcript := (LiteralByteProtocol.protocol D).transcript H before.2.1.statement before.2.1.proof 33
  have valid : ∀ n (bound : n<transcript.rounds.length),
      LiteralTranscript.valid n (transcript.rounds[n]'bound).1 := by
    intro n hn
    have len : transcript.rounds.length=33 := LiteralByteRunFacts.transcript_round D H _ _ 33
    have small : n<33 := by omega
    have entry := LiteralByteRunFacts.transcript_index D H before.2.1.statement before.2.1.proof 33 n small
    rw [List.getElem?_eq_getElem hn] at entry
    have msg := congrArg Prod.fst (Option.some.inj entry)
    rw [msg,first_proof rust P H p parsed]
    exact parsed_valid p n small
  have restored := OraclePortRowsCanonicalC6.rows p q (build D (view before)) transcript valid
  rw [restored]
  have pub : (eval H (source D rust P)).2.1.1=before.2.1.statement := by
    simp only [source_eval,OraclePortFrozen2Join.annotatedWith_eval,view,enrich,before]
  have pf : (eval H (source D rust P)).2.1.2=
      RawCutTranscriptRun.proof (build D (view before)) before.2.1.proof := by
    simp only [source_eval,OraclePortFrozen2Join.annotatedWith_eval,view,enrich,before]
  rw [pub,pf,RawCutTranscriptRun.transcript_eq]
  rfl

/-- Transport terminal checks through the actual two-pass carrier. Named to
keep large native-call compositions from reducing concrete transcript33. -/
theorem checks_to_source (D : LiteralByteProtocol.Decoder) (rust : Verifier) (P : ByteProver)
    (H : Bytes → State) (p : OraclePortCompactDraft.Parsed) (q : Fin 22 → Fin 262144)
    (parsed : OraclePortCompactDraft.parse (first rust P H).2.1.stored=some p)
    (checked : Nonempty (LiteralAcceptanceTerminal.Checks
      (first rust P H).2.1.statement
      (OraclePortReaderPlumbingC6.reword (build D (view (first rust P H)))
        (OraclePortStoredDecisionDraftC4.typedRows p q
          (Port6AUTH_Frames.reached D H (first rust P H).2.1.statement (first rust P H).2.1.proof))))) :
    Nonempty (LiteralAcceptanceTerminal.Checks (eval H (source D rust P)).2.1.1
      ((LiteralByteProtocol.protocol D).transcript H (eval H (source D rust P)).2.1.1
        (eval H (source D rust P)).2.1.2 33).rounds) := by
  have rowEq := rows D rust P H p q parsed
  rw [rowEq] at checked
  have pub : (eval H (source D rust P)).2.1.1=(first rust P H).2.1.statement := by
    simp only [source_eval,OraclePortFrozen2Join.annotatedWith_eval,view,enrich]
  rw [pub] at checked ⊢
  exact checked

#print axioms erased_statement
#print axioms reached_statement
#print axioms checks_to_source

#print axioms transcript_statement
#print axioms parsed_valid
#print axioms canon_parsed
#print axioms first_proof
#print axioms rows
end AspisR1.Port7CLEAN_Carrier
end
