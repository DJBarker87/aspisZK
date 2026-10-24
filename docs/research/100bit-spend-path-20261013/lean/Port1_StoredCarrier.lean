import Port1_DriverSubstitution
import MultiproofConeSemanticRows

/-! Source-indexed byte submissions. Parsing is the retained strict compact
parser; the semantic parser's source refinement is imported, not a free
logical-proof parameter. Malformed/oversized values have explicit totalization
branches. No source acceptance or source/parser agreement is claimed here. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port1_StoredCarrier
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open OraclePortStoredExperimentC4 OraclePortRuntimeBindingC7
open OraclePortCompactDraft

/-- Both fields range over arbitrary byte lists, including malformed inputs. -/
structure Submission where
  publicBytes : Bytes
  stored : Bytes
abbrev ByteProver := Program Bytes State Submission

/-- Oversized public inputs cannot fit the existing model address carrier.
This totalization is logical only; runtime admission must justify its use. -/
def statement (s : Submission) : LiteralTranscript.Public :=
  if h : 75 + s.publicBytes.length ≤ SelectedTranscriptParams.L then
    ⟨s.publicBytes, h, s.stored[8]?.getD 0⟩
  else ⟨[], by decide, s.stored[8]?.getD 0⟩

def payload (b : Bytes) : LiteralTranscript.BytesMessage :=
  if h : b.length ≤ SelectedTranscriptParams.D then ⟨b,h⟩ else ⟨[], by decide⟩

def parsedProof (p : Parsed) : LiteralProtocol.Proof := fun row =>
  if row = 0 then .initial (fun j => (root0 p)[j.val]?.getD 0) (fun _ => 0)
  else if row = 2 then .c2 (payload (rowBytes p row)) (fun _ _ => 0)
  else if row = 30 then .second (payload (rowBytes p row)) (fun _ => 0)
  else .payload (payload (rowBytes p row))

/-- The only logical proof is computed from submitted bytes. Zero words are
annotation placeholders, not adversary-chosen commitment witnesses. -/
def proof (stored : Bytes) : LiteralProtocol.Proof :=
  match parse stored with
  | some p => parsedProof p
  | none => fun _ => .payload ⟨[], by decide⟩

def input (s : Submission) : Input := ⟨statement s, proof s.stored, s.stored⟩
def lift (P : ByteProver) : Prover := bind P (fun s => .done (input s))

/-- Annotation/canonical retagging may replace ghost words, while every
physical byte and erased logical message stays source-indexed. -/
def Carried (i : Input) : Prop := ∃ s : Submission,
  i.statement = (input s).statement ∧ i.stored = s.stored ∧
    ∀ row, LiteralTranscript.erase (i.proof row) =
      LiteralTranscript.erase ((input s).proof row)

theorem input_carried (s : Submission) : Carried (input s) := ⟨s,rfl,rfl,fun _ => rfl⟩

theorem parsed_proof (s : Submission) (p : Parsed) (h : parse s.stored = some p) :
    (input s).proof = parsedProof p := by simp only [input,proof,h]

theorem public_bytes (s : Submission)
    (h : 75 + s.publicBytes.length ≤ SelectedTranscriptParams.L) :
    (input s).statement.pubBytes = s.publicBytes := by simp only [input,statement,dif_pos h]

theorem lift_eval (P : ByteProver) (H : Bytes → State) :
    eval H (lift P) = ((eval H P).1,input (eval H P).2) := by
  simp only [lift,eval_bind,eval,List.append_nil]

theorem lift_carried (P : ByteProver) (H : Bytes → State) :
    Carried (eval H (lift P)).2 := by rw [lift_eval]; exact input_carried _

theorem enrich_carried (w : CanonicalCutEnrichedTranscript.Words) (i : Input)
    (h : Carried i) : Carried (enrich w i) := by
  obtain ⟨s,statement,stored,rows⟩ := h
  refine ⟨s,statement,stored,fun row => ?_⟩
  exact (CanonicalCutEnrichedTranscript.erase_enrichMessage w (i.proof row)).trans (rows row)

theorem canon_carried (i : Input) (h : Carried i) :
    Carried (OraclePortStoredAdmissionC4.canonInput i) := by
  obtain ⟨s,statement,stored,rows⟩ := h
  exact ⟨s,statement,stored,fun row => (R16CanonReduction.erase_proof i.proof row).trans (rows row)⟩

theorem canon_lift_carried (P : ByteProver) (H : Bytes → State) :
    Carried (eval H (OraclePortStoredAdmissionC4.canon (lift P))).2 := by
  rw [OraclePortStoredAdmissionC4.canon_eval]
  exact canon_carried _ (lift_carried P H)

/-- This law speaks only of arguments physically supplied to Rust. -/
def Physical (rust : Verifier) : Prop := ∀ i j : Input,
  i.statement.pubBytes = j.statement.pubBytes → i.stored = j.stored → rust i = rust j

theorem driver_physical (adapter : AdapterRw.Ops) (impl : VTop_OracleCode.Implementation)
    {Hash : Type} (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash) :
    Physical (Port1_Driver.rust adapter impl D hash) := by
  intro i j pub stored
  simp only [Port1_Driver.rust,pub,stored]

#print axioms input_carried
#print axioms parsed_proof
#print axioms public_bytes
#print axioms lift_eval
#print axioms lift_carried
#print axioms enrich_carried
#print axioms canon_carried
#print axioms canon_lift_carried
#print axioms driver_physical
end AspisR1.Port1_StoredCarrier
end
