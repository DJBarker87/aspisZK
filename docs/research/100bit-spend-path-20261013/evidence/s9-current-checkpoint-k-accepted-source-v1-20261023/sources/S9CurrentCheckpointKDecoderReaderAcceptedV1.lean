import S9CurrentCheckpointKDecoderAcceptedV1
import S9ReaderKActualQMCanonicalV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9CurrentCheckpointKDecoderReaderAcceptedV1
open AspisR1Stage2
open AspisR1S9CurrentCheckpointKDecoderCMMapV1
open AspisR1S9CurrentCheckpointKDecoderAcceptedV1

/-- Nominal output copy only; all four current source words are retained. -/
def toStage2QM (q : CurQM) : aspis_core.field.QM31 :=
  ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩

def actualCheckpointDecoder (bytes : Slice U8) : Result (Option aspis_core.field.QM31) :=
  mapResult (Option.map toStage2QM)
    (AspisR1S9CurrentCheckpointKDecoderV1.field.QM31.from_le_bytes bytes)

/-- Same-value accepted-source decoder transfer; rejection traces are not asserted equal. -/
theorem actual_decoder_success_retained (bytes : Slice U8) (q : aspis_core.field.QM31)
    (h : actualCheckpointDecoder bytes = .ok (some q)) :
    AspisR1S9ReaderKActualQMCanonicalV1.checkpointQMDecoder bytes = .ok (some q) := by
  unfold actualCheckpointDecoder at h
  cases hd : AspisR1S9CurrentCheckpointKDecoderV1.field.QM31.from_le_bytes bytes with
  | fail e => simp [hd,mapResult,AspisR1S9SourceResultTransportV1.mapResult] at h
  | div => simp [hd,mapResult,AspisR1S9SourceResultTransportV1.mapResult] at h
  | ok o =>
    cases o with
    | none => simp [hd,mapResult,AspisR1S9SourceResultTransportV1.mapResult] at h
    | some value =>
      simp only [hd,mapResult,AspisR1S9SourceResultTransportV1.mapResult,Option.map_some] at h
      have he : toStage2QM value = q := by
        exact Option.some.inj (Result.ok.inj h)
      subst q
      have hold := qm_success_to_old bytes value hd
      unfold AspisR1S9ReaderKActualQMCanonicalV1.checkpointQMDecoder
      rw [hold]
      rfl

private theorem bind_success {A B : Type} (m : Result A) (k : A → Result B) (out : B)
    (h : (do let x ← m; k x) = ok out) : ∃ x, m = ok x ∧ k x = ok out := by
  cases m with
  | ok x => exact ⟨x,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

private theorem pair_let_beta {A B C : Type} (a : A) (b : B) (k : A → B → C) :
    (let (a1,b1) := (a,b); k a1 b1) = k a b := rfl

private def optionOkOr (value : Option aspis_core.field.QM31) :
    Result (core.result.Result aspis_core.field.QM31 verifier.Error) :=
  match value with | none => .ok (.Err .Checkpoint) | some q => .ok (.Ok q)

/-- Exact Reader.k operation shape with the actual current source decoder;
raw reading and its current caller/source-runtime binding remain explicit. -/
def readerKCurrent (raw : (n : Usize) → verifier.Reader → Result (Array U8 n × verifier.Reader))
    (reader : verifier.Reader) :
    Result (core.result.Result aspis_core.field.QM31 verifier.Error × verifier.Reader) := do
  let (bytes,reader1) ← raw 16#usize reader
  let slice ← lift (Array.to_slice bytes)
  let value ← actualCheckpointDecoder slice
  let result ← optionOkOr value
  .ok (result,reader1)

/-- Every successful current reader call has the same retained-reader value and cursor.
No hypothesis of decoder correctness/canonicality or of a child read success is added. -/
theorem readerKCurrent_success_retained
    (raw : (n : Usize) → verifier.Reader → Result (Array U8 n × verifier.Reader))
    (reader reader1 : verifier.Reader) (q : aspis_core.field.QM31)
    (h : readerKCurrent raw reader = .ok (.Ok q,reader1)) :
    AspisR1S9ReaderKActualQMCanonicalV1.readerK raw reader = .ok (.Ok q,reader1) := by
  unfold readerKCurrent at h
  obtain ⟨pair,hraw,h⟩ := bind_success _ _ _ h
  rcases pair with ⟨bytes,r0⟩
  simp only [lift,bind_tc_ok] at h
  obtain ⟨o,hdecode,h⟩ := bind_success _ _ _ h
  cases o with
  | none => simp only [optionOkOr,bind_tc_ok] at h; cases h
  | some value =>
    have hold := actual_decoder_success_retained bytes.to_slice value hdecode
    simp only [optionOkOr,bind_tc_ok] at h
    have hp := Result.ok.inj h
    have hv : value = q := core.result.Result.Ok.inj (congrArg Prod.fst hp)
    have hr : r0 = reader1 := congrArg Prod.snd hp
    subst q
    subst reader1
    unfold AspisR1S9ReaderKActualQMCanonicalV1.readerK
    rw [hraw]
    simp only [bind_tc_ok,lift]
    have htail : (do
        let o ← AspisR1S9ReaderKActualQMCanonicalV1.checkpointQMDecoder bytes.to_slice
        let result ← optionOkOr o
        .ok (result,r0)) = .ok (.Ok value,r0) := by
      rw [hold]
      rfl
    exact htail

theorem readerKCurrent_success_canonical
    (raw : (n : Usize) → verifier.Reader → Result (Array U8 n × verifier.Reader))
    (reader reader1 : verifier.Reader) (q : aspis_core.field.QM31)
    (h : readerKCurrent raw reader = .ok (.Ok q,reader1)) :
    AspisR1S9ReaderKActualQMCanonicalV1.Canonical q :=
  AspisR1S9ReaderKActualQMCanonicalV1.readerK_success_canonical raw reader reader1 q
    (readerKCurrent_success_retained raw reader reader1 q h)

#print axioms actual_decoder_success_retained
#print axioms readerKCurrent_success_retained
#print axioms readerKCurrent_success_canonical
end AspisR1S9CurrentCheckpointKDecoderReaderAcceptedV1
