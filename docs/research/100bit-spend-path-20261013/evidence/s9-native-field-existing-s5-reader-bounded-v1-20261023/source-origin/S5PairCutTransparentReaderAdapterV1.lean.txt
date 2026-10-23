import S5PairCutFieldCallbackV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S5PairCutTransparentReaderV1

abbrev PairWide := AspisR1S5PairCutFieldCallbackV1.PairWide
abbrev RecordWide := AspisR1CurrentWide.Proof.RecordWide
open AspisR1S5PairCutFieldCallbackV1

def recordToPair (x : RecordWide) : PairWide :=
  finishToPair (AspisR1CurrentWide.Proof.recordWideToFinish x)

/-- Result-preserving nominal map for the selected actual record decoder. -/
def mapDecodedRecord (x : Result (Option RecordWide)) : Result (Option PairWide) :=
  do
    let value ← x
    ok (Option.map recordToPair value)

def actualPairDecoder (bytes : Slice U8) : Result (Option PairWide) :=
  mapDecodedRecord
    (AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes bytes)

def actualPairReader (bytes : Slice U8) (i : Usize) : Result PairWide := do
  let value ← AspisR1WeightsFieldCurrent.weights.field
    AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes bytes i
  ok (recordToPair value)

theorem mapDecoder_then_unwrap
    (decoded : Result (Option RecordWide)) :
    (do
      let o ← mapDecodedRecord decoded
      core.option.Option.unwrap o) =
    (do
      let o ← decoded
      let value ← core.option.Option.unwrap o
      ok (recordToPair value)) := by
  cases decoded with
  | fail e => rfl
  | div => rfl
  | ok optionValue =>
    cases optionValue with
    | none => rfl
    | some value => rfl

/-- The emitted field reader, abstracted only over its final decoder operation.
The operation order mirrors the transparent Aeneas body: checked offset
arithmetic, range indexing, decoding, then Option unwrap. -/
def readerBody (decode : Slice U8 → Result (Option PairWide))
    (bytes : Slice U8) (i : Usize) : Result PairWide := do
  let i1 ← i * 32#usize
  let i2 ← i + 1#usize
  let i3 ← i2 * 32#usize
  let s ← core.slice.index.Slice.index
    (core.slice.index.SliceIndexRangeUsizeSlice U8) bytes
    { start := i1, «end» := i3 }
  let o ← decode s
  core.option.Option.unwrap o

/-- The decoder-parameterized reader is definitionally the selected exact
WeightsField selector. The source checker in the evidence packet verifies the
emitted candidate body has this same ordered operation skeleton. -/
theorem readerBody_eq_selectedSelector
    (decode : Slice U8 → Result (Option PairWide))
    (bytes : Slice U8) (i : Usize) :
    readerBody decode bytes i =
      AspisR1WeightsFieldCurrent.weights.field decode bytes i := by
  rfl

theorem readerBody_actualDecoder_eq_reader
    (bytes : Slice U8) (i : Usize) :
    readerBody actualPairDecoder bytes i = actualPairReader bytes i := by
  unfold readerBody actualPairDecoder actualPairReader
  simp only [AspisR1WeightsFieldCurrent.weights.field]
  -- Rewrite only the final decoder/unwrap distribution; the common offset
  -- and slice-index prefix is definitionally identical.
  simp_rw [mapDecoder_then_unwrap]
  simp only [bind_assoc_eq]

/-- Feeding the selected strict record decoder through the explicit nominal
coordinate map makes the emitted-reader model equal the checked retained
callback. No equality is asserted against the old arbitrary FunsExternal
interpretation or the unreachable extraction-harness decoder stub. -/
theorem actualReader_eq_checkedCallback
    (bytes : Slice U8) (i : Usize) :
    readerBody actualPairDecoder bytes i = checkedFieldCallback bytes i := by
  rw [readerBody_actualDecoder_eq_reader]
  unfold actualPairReader checkedFieldCallback AspisR1CurrentWide.Proof.finishField
  simp only [recordToPair, bind_assoc_eq, bind_tc_ok]

#print axioms readerBody_eq_selectedSelector
#print axioms readerBody_actualDecoder_eq_reader
#print axioms actualReader_eq_checkedCallback
end AspisR1S5PairCutTransparentReaderV1
