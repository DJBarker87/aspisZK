import R1LiteralSemanticCodecBridge
import R1SelectedSemanticPrefixFacts
import R1LiteralTypedContext

/-! Relate strict semantic record bytes and
the literal C2 word to SemanticPayloadView. The record sequence, constructor
schedule and ordinary challenge coordinates are explicit representation
premises, not consequences asserted about Rust verification. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.LiteralSemanticPayloadBridge

open R0P.Mask R0P.SemSource
open AspisR1.SemanticRecordCodec
open AspisR1.LiteralSemanticCodecBridge

abbrev E := LiteralSemanticPrefix.E
abbrev State := SemanticPayloadView.State
abbrev Bytes := SemanticRecordCodec.Bytes
abbrev Message := LiteralTranscript.Message
abbrev Challenge := LiteralTranscript.Challenge
abbrev Entry := SemanticPrefixCodec.Entry
abbrev Full := SemanticPrefixCodec.Full
abbrev C2Word := LiteralTranscript.C2Word

/-- Only the message at logical row two may carry this word. The relation
does not recover a word from a root or from a later oracle table. -/
def CarriesC2 (word : C2Word) (m : Message) : Prop :=
  ∀ bs actual, m = .c2 bs actual → actual = word

theorem callback_toMessage
    (eK : AspisV8R15.ExactTowerBase.QM31Exact →+* E)
    (row : Fin 25) (payload : RowPayload row) (m : Message) (word : C2Word)
    (hv : LiteralTranscript.valid row.val m) (hc2 : CarriesC2 word m) :
    SemanticPayloadView.toMessage (callback eK m) payload.val =
      SemanticPayloadView.toMessage (fun _ => LiteralSemanticPrefix.c2Pair eK word) payload.val := by
  rcases payload with ⟨payload, hp⟩
  cases payload with
  | empty => rfl
  | maskSum value => rfl
  | polynomial coefficients => rfl
  | c2Root root =>
      have hr : row.val = 2 := by simpa [validRow] using hp
      cases m with
      | initial c1 c1word => simp [LiteralTranscript.valid, hr] at hv
      | payload bs => simp [LiteralTranscript.valid, hr] at hv
      | second bs v => simp [LiteralTranscript.valid, hr] at hv
      | c2 bs actual =>
          have he := hc2 bs actual rfl
          subst actual
          rfl

theorem parseMessage_of_payload
    (eK : AspisV8R15.ExactTowerBase.QM31Exact →+* E)
    (row : Fin 25) (payload : RowPayload row) (m : Message) (word : C2Word)
    (hv : LiteralTranscript.valid row.val m)
    (hbytes : record m = SemanticRecordCodec.encode payload)
    (hc2 : CarriesC2 word m) :
    LiteralSemanticPrefix.parseMessage eK row m =
      some (SemanticPayloadView.toMessage
        (fun _ => LiteralSemanticPrefix.c2Pair eK word) payload.val) := by
  rw [parseMessage_eq_decode, if_pos hv, hbytes, SemanticRecordCodec.decode_encode]
  exact congrArg some (callback_toMessage eK row payload m word hv hc2)

def literalPairs (messages : Fin 25 → Message) (challenges : Fin 25 → E)
    (states : Fin 25 → State) : List (Message × Challenge) :=
  List.ofFn fun i => (messages i, (TranscriptView.Value.ordinary (challenges i), states i))

/-- Induction over the accepted codec's sequential entries. This reuses the
literal reader; it is not another parser. -/
theorem read_entries
    (eK : AspisV8R15.ExactTowerBase.QM31Exact →+* E) (word : C2Word)
    (message : Entry → Message) (challenge : Entry → E) (state : Entry → State)
    (row : Nat) (entries : List Entry)
    (hrows : entries.map Sigma.fst = List.range' row entries.length)
    (hv : ∀ e ∈ entries, LiteralTranscript.valid e.1 (message e))
    (hb : ∀ e ∈ entries, record (message e) = SemanticPrefixCodec.encodeEntry e)
    (hc2 : ∀ e ∈ entries, CarriesC2 word (message e)) :
    LiteralSemanticPrefix.read eK row
      (entries.map fun e => (message e, (TranscriptView.Value.ordinary (challenge e), state e))) =
      some (entries.map fun e =>
        (SemanticPayloadView.toMessage (fun _ => LiteralSemanticPrefix.c2Pair eK word)
          e.2.value.val, challenge e)) := by
  induction entries generalizing row with
  | nil => rfl
  | cons first tail ih =>
      rcases first with ⟨j, payload⟩
      simp only [List.map_cons, List.length_cons, List.range'_succ] at hrows
      have hj : j = row := (List.cons.inj hrows).1
      subst j
      have ht := (List.cons.inj hrows).2
      have hp := parseMessage_of_payload eK ⟨row, payload.isLt⟩ payload.value
        (message ⟨row, payload⟩) word
        (hv ⟨row, payload⟩ (List.mem_cons_self ..))
        (hb ⟨row, payload⟩ (List.mem_cons_self ..))
        (hc2 ⟨row, payload⟩ (List.mem_cons_self ..))
      have htail := ih (row + 1) ht
        (fun e he => hv e (List.mem_cons_of_mem _ he))
        (fun e he => hb e (List.mem_cons_of_mem _ he))
        (fun e he => hc2 e (List.mem_cons_of_mem _ he))
      simp [LiteralSemanticPrefix.read, payload.isLt, hp, htail]

theorem read_of_payloads
    (eK : AspisV8R15.ExactTowerBase.QM31Exact →+* E) (word : C2Word)
    (payloads : Full) (messages : Fin 25 → Message)
    (challenges : Fin 25 → E) (states : Fin 25 → State)
    (hv : ∀ i, LiteralTranscript.valid i.val (messages i))
    (hb : ∀ i, record (messages i) = SemanticRecordCodec.encode (payloads i))
    (hc2 : ∀ i, CarriesC2 word (messages i)) :
    LiteralSemanticPrefix.read eK 0 (literalPairs messages challenges states) =
      some (SemanticPayloadView.pairs
        (fun _ => LiteralSemanticPrefix.c2Pair eK word) payloads challenges) := by
  let message : Entry → Message := fun e => messages ⟨e.1, e.2.isLt⟩
  let challenge : Entry → E := fun e => challenges ⟨e.1, e.2.isLt⟩
  let state : Entry → State := fun e => states ⟨e.1, e.2.isLt⟩
  have hv' : ∀ e ∈ SemanticPrefixCodec.entriesOf payloads,
      LiteralTranscript.valid e.1 (message e) := by
    intro e he
    rcases List.mem_ofFn.mp he with ⟨i, rfl⟩
    exact hv i
  have hb' : ∀ e ∈ SemanticPrefixCodec.entriesOf payloads,
      record (message e) = SemanticPrefixCodec.encodeEntry e := by
    intro e he
    rcases List.mem_ofFn.mp he with ⟨i, rfl⟩
    exact hb i
  have hc2' : ∀ e ∈ SemanticPrefixCodec.entriesOf payloads,
      CarriesC2 word (message e) := by
    intro e he
    rcases List.mem_ofFn.mp he with ⟨i, rfl⟩
    exact hc2 i
  have hrows : (SemanticPrefixCodec.entriesOf payloads).map Sigma.fst =
      List.range' 0 (SemanticPrefixCodec.entriesOf payloads).length := by
    simpa only [SemanticPrefixCodec.entriesOf_length] using
      SemanticPrefixCodec.entriesOf_rows payloads
  have hr := read_entries eK word message challenge state 0
    (SemanticPrefixCodec.entriesOf payloads) hrows hv' hb' hc2'
  simpa [message, challenge, state, literalPairs, SemanticPayloadView.pairs,
    SemanticPrefixCodec.entriesOf, List.map_ofFn] using hr

theorem record_eq_of_decodeFull (messages : Fin 25 → Message) (payloads : Full)
    (h : SemanticPrefixCodec.decodeFull
      (List.ofFn fun i => record (messages i)) = some payloads) (i : Fin 25) :
    record (messages i) = SemanticRecordCodec.encode (payloads i) := by
  have hb := SemanticPrefixCodec.encodeFull_of_decodeFull _ _ h
  have hf : (fun j : Fin 25 => SemanticRecordCodec.encode (payloads j)) =
      (fun j : Fin 25 => record (messages j)) := by
    apply List.ofFn_injective
    simpa only [SemanticPrefixCodec.encodeFull, SemanticPrefixCodec.entriesOf,
      List.map_ofFn, Function.comp_def, SemanticPrefixCodec.encodeEntry] using hb
  exact (congrFun hf i).symm

/-- Once the literal records successfully decode, no pointwise re-encoding
premise is needed: the accepted codec's back law supplies it. -/
theorem read_of_decodeFull
    (eK : AspisV8R15.ExactTowerBase.QM31Exact →+* E) (word : C2Word)
    (payloads : Full) (messages : Fin 25 → Message)
    (challenges : Fin 25 → E) (states : Fin 25 → State)
    (hv : ∀ i, LiteralTranscript.valid i.val (messages i))
    (hc2 : ∀ i, CarriesC2 word (messages i))
    (hdecode : SemanticPrefixCodec.decodeFull
      (List.ofFn fun i => record (messages i)) = some payloads) :
    LiteralSemanticPrefix.read eK 0 (literalPairs messages challenges states) =
      some (SemanticPayloadView.pairs
        (fun _ => LiteralSemanticPrefix.c2Pair eK word) payloads challenges) :=
  read_of_payloads eK word payloads messages challenges states hv
    (record_eq_of_decodeFull messages payloads hdecode) hc2

theorem lifted_read_of_decodeFull
    (eK : AspisV8R15.ExactTowerBase.QM31Exact →+* E) (word : C2Word)
    (payloads : Full) (messages : Fin 25 → Message)
    (challenges : Fin 25 → E) (states : Fin 25 → State)
    (hv : ∀ i, LiteralTranscript.valid i.val (messages i))
    (hc2 : ∀ i, CarriesC2 word (messages i))
    (hdecode : SemanticPrefixCodec.decodeFull
      (List.ofFn fun i => record (messages i)) = some payloads)
    (parsed : List (SemMsgZ E × E))
    (hread : LiteralSemanticPrefix.read eK 0
      (literalPairs messages challenges states) = some parsed) :
    SelectedSemanticPrefixFacts.lift parsed =
      SemanticPayloadView.rounds
        (fun _ => LiteralSemanticPrefix.c2Pair eK word) payloads challenges := by
  have he := read_of_decodeFull eK word payloads messages challenges states hv hc2 hdecode
  have hp : parsed = SemanticPayloadView.pairs
      (fun _ => LiteralSemanticPrefix.c2Pair eK word) payloads challenges :=
    Option.some.inj (hread.symm.trans he)
  rw [hp]
  rfl

theorem valid_c2_row (row : Nat) (bs : LiteralTranscript.BytesMessage) (word : C2Word)
    (h : LiteralTranscript.valid row (.c2 bs word)) : row = 2 := by
  cases row with
  | zero => simp [LiteralTranscript.valid] at h
  | succ n =>
      cases n with
      | zero => simp [LiteralTranscript.valid] at h
      | succ n =>
          cases n with
          | zero => rfl
          | succ n => simp [LiteralTranscript.valid] at h

theorem carriesC2_of_row_two (messages : Fin 25 → Message) (word : C2Word)
    (hv : ∀ i, LiteralTranscript.valid i.val (messages i))
    (hrow2 : ∃ bs, messages ⟨2, by omega⟩ = .c2 bs word) :
    ∀ i, CarriesC2 word (messages i) := by
  intro i bs actual hm
  have hc : LiteralTranscript.valid i.val (.c2 bs actual) := by rw [← hm]; exact hv i
  have hi : i = (⟨2, by omega⟩ : Fin 25) := Fin.ext (valid_c2_row i.val bs actual hc)
  subst i
  obtain ⟨atTwo, ht⟩ := hrow2
  have he : LiteralTranscript.Message.c2 bs actual =
      LiteralTranscript.Message.c2 atTwo word := hm.symm.trans ht
  cases he
  rfl

theorem read_of_decodeFull_atC2
    (eK : AspisV8R15.ExactTowerBase.QM31Exact →+* E) (word : C2Word)
    (payloads : Full) (messages : Fin 25 → Message)
    (challenges : Fin 25 → E) (states : Fin 25 → State)
    (hv : ∀ i, LiteralTranscript.valid i.val (messages i))
    (hrow2 : ∃ bs, messages ⟨2, by omega⟩ = .c2 bs word)
    (hdecode : SemanticPrefixCodec.decodeFull
      (List.ofFn fun i => record (messages i)) = some payloads) :
    LiteralSemanticPrefix.read eK 0 (literalPairs messages challenges states) =
      some (SemanticPayloadView.pairs
        (fun _ => LiteralSemanticPrefix.c2Pair eK word) payloads challenges) :=
  read_of_decodeFull eK word payloads messages challenges states hv
    (carriesC2_of_row_two messages word hv hrow2) hdecode

theorem pair_fst_fullWords
    (eM : ExactLeafFieldCodec.M31Exact →+* E)
    (eK : ExactLeafFieldCodec.QM31Exact →+* E)
    (c1 : LiteralTranscript.C1Word) (c2 : C2Word) :
    (LiteralSemanticPrefix.c2Pair eK c2).1 =
      LiteralTypedContext.fullWords eM eK c1 c2 26 := by
  funext i
  simp [LiteralSemanticPrefix.c2Pair, LiteralTypedContext.fullWords, LiteralTypedWords.word]

theorem pair_snd_fullWords
    (eM : ExactLeafFieldCodec.M31Exact →+* E)
    (eK : ExactLeafFieldCodec.QM31Exact →+* E)
    (c1 : LiteralTranscript.C1Word) (c2 : C2Word) :
    (LiteralSemanticPrefix.c2Pair eK c2).2 =
      LiteralTypedContext.fullWords eM eK c1 c2 27 := by
  funext i
  simp [LiteralSemanticPrefix.c2Pair, LiteralTypedContext.fullWords, LiteralTypedWords.word]

theorem pair_c2Base
    (eM : ExactLeafFieldCodec.M31Exact →+* E)
    (eK : ExactLeafFieldCodec.QM31Exact →+* E)
    (c1 : LiteralTranscript.C1Word) (c2 : C2Word) :
    c2Base (LiteralTypedWords.laneSubfield eM eK)
      (LiteralSemanticPrefix.c2Pair eK c2).1
      (LiteralSemanticPrefix.c2Pair eK c2).2 := by
  rw [pair_fst_fullWords eM eK c1 c2, pair_snd_fullWords eM eK c1 c2]
  exact LiteralTypedContext.c2Base_full eM eK c1 c2

theorem pair_c2Words
    (eM : ExactLeafFieldCodec.M31Exact →+* E)
    (eK : ExactLeafFieldCodec.QM31Exact →+* E)
    (pub : R0P.Public E) (hpub : R0P.PublicBase eM.fieldRange pub)
    (c1 : LiteralTranscript.C1Word) (c2 : C2Word) (extra : Fin 29 → E) :
    c2Words (LiteralTypedContext.context eM eK pub hpub c1 extra)
      (LiteralSemanticPrefix.c2Pair eK c2).1
      (LiteralSemanticPrefix.c2Pair eK c2).2 =
      LiteralTypedContext.fullWords eM eK c1 c2 := by
  rw [pair_fst_fullWords eM eK c1 c2, pair_snd_fullWords eM eK c1 c2]
  exact LiteralTypedContext.c2Words_full eM eK pub hpub c1 c2 extra

-- Consumer: rewrite a parsed literal semantic list using
-- lifted_read_of_decodeFull; supply pair_c2Base to the already existing
-- SemanticPayloadOpeningView.opening_view_of_payloads. Circle premises,
-- opening-message representation and verifier acceptance remain external.

#print axioms callback_toMessage
#print axioms parseMessage_of_payload
#print axioms read_entries
#print axioms read_of_payloads
#print axioms record_eq_of_decodeFull
#print axioms read_of_decodeFull
#print axioms lifted_read_of_decodeFull
#print axioms carriesC2_of_row_two
#print axioms read_of_decodeFull_atC2
#print axioms pair_c2Base
#print axioms pair_c2Words

end AspisR1.LiteralSemanticPayloadBridge
end


