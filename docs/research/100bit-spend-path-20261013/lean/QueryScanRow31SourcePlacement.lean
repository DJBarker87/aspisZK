import R1LiteralQuerySample
import R1LiteralByteRunFacts
import RecordedBinaryExperimentBin

/-! R4 row31 follows from R16's existing placement into the actual fixed
sampler transcript. This does not instantiate R16 for the frozen Rust source. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.QueryScanRow31SourcePlacement
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open RawCutProverCompiler RawCutTranscriptRun
open RecordedBinaryExperimentBin DecoderInstanceBoundaryBin

/-- Unpack only the strict query reader's successful branch. -/
theorem decode_shape (xs : List Nat) (q : Fin 22 → Fin 262144)
    (h : LiteralQueryRead.decode xs = some q) :
    xs.Nodup ∧ xs.length = 22 ∧ ∀ x ∈ xs, x < 262144 := by
  unfold LiteralQueryRead.decode at h
  split_ifs at h with hv
  · exact hv

/-- A successful valid row-31 entry of any protocol transcript has the shape.
No acceptance, extractor, or source premise is needed for this model fact. -/
theorem transcript_row31_shape (D : LiteralByteProtocol.Decoder)
    (H : Bytes → State) (pub : LiteralTranscript.Public)
    (pf : LiteralProtocol.Proof) (n : Nat) (hn : 31 < n)
    (m : LiteralTranscript.Message) (xs : List Nat) (state : State)
    (hrow : ((LiteralByteProtocol.protocol D).transcript H pub pf n).rounds[31]? =
      some (m, (TranscriptView.Value.queries (.ok xs), state)))
    (hm : LiteralTranscript.valid 31 m) :
    xs.Nodup ∧ xs.length = 22 ∧ ∀ x ∈ xs, x < 262144 := by
  have hindex := LiteralByteRunFacts.transcript_index D H pub pf n 31 hn
  have he := Option.some.inj (hindex.symm.trans hrow)
  have hmessage : pf 31 = m := congrArg Prod.fst he
  have hout := congrArg Prod.snd he
  rw [hmessage] at hout
  obtain ⟨q, hq⟩ := LiteralQuerySample.valid_row31_success_decodes H
    ((LiteralByteProtocol.protocol D).transcript H pub pf 31) m xs state hm hout
  exact decode_shape xs q hq

/-- Only the two existing row-31 R16 fields are consumed. -/
theorem compiled_row31_shape (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover)
    (H : Bytes → State) (i : SourceInputs)
    (hrow : (compiledRows D d P H)[31]? = some (i.m31,
      (TranscriptView.Value.queries (.ok i.queryBytes), i.state31)))
    (hm : LiteralTranscript.valid 31 i.m31) :
    i.queryBytes.Nodup ∧ i.queryBytes.length = 22 ∧
      ∀ x ∈ i.queryBytes, x < 262144 := by
  exact transcript_row31_shape D H (compiledPublic D d P H)
    (annotatedRun D d P H).2.1.2 33 (by omega)
    i.m31 i.queryBytes i.state31 hrow hm

/-- The whole R4 row31 premise is a consequence of the already retained R16.
Public parsing, row32 and row32 validity are unused by this implication. -/
theorem instanceFields_row31 (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover)
    (H : Bytes → State) (i : SourceInputs) (h : InstanceFields D d P H i) :
    i.queryBytes.Nodup ∧ i.queryBytes.length = 22 ∧
      ∀ x ∈ i.queryBytes, x < 262144 :=
  compiled_row31_shape D d P H i h.2.1 h.2.2.2.1

#print axioms decode_shape
#print axioms transcript_row31_shape
#print axioms compiled_row31_shape
#print axioms instanceFields_row31
end AspisR1.QueryScanRow31SourcePlacement
end
