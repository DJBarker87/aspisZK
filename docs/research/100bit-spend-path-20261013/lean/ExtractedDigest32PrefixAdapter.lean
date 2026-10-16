import AspisR1PublicPreparation.Funs
import ExtractedPrefixTypedFull

/-! Concrete nominal adapter for the accepted actual Prefix parser. The Rust
Prefix::parse body is unchanged and re-pinned; no arbitrary parser callback or
record byte identity is introduced by this adapter. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1PublicPreparation.PrefixAdapter
open r1_wire
abbrev OldPrefix := AspisR1PrefixAggregateParser.r1_wire.Prefix
abbrev OldError := AspisR1PrefixAggregateParser.r1_wire.Error

def toOld (pre : Prefix) : OldPrefix := ⟨pre.c1_root, pre.records⟩
def fromOld (pre : OldPrefix) : Prefix := ⟨pre.c1_root, pre.records⟩
@[simp] theorem toOld_fromOld (pre : OldPrefix) : toOld (fromOld pre) = pre := by cases pre; rfl
@[simp] theorem fromOld_toOld (pre : Prefix) : fromOld (toOld pre) = pre := by cases pre; rfl

def errorFromOld : OldError → r1_wire.Error
  | .Allocation => .Allocation
  | .RowOrder expected actual => .RowOrder expected actual
  | .InvalidRow => .InvalidRow
  | .Tag row => .Tag row
  | .Length row => .Length row
  | .NonCanonical row value => .NonCanonical row value
  | .Boundary value => .Boundary value
  | .Terminal => .Terminal
  | .EqualCirclePoints => .EqualCirclePoints
  | .TrailingBytes => .TrailingBytes
  | .Public => .Public

/-- A fixed actual parser, with only its nominal Prefix/Error carriers mapped.
This definition can instantiate an explicit downstream caller boundary. -/
def parseAccepted (bytes : Slice U8) : Result (core.result.Result Prefix r1_wire.Error) := do
  let result ← AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes
  match result with
  | .Ok pre => ok (.Ok (fromOld pre))
  | .Err error => ok (.Err (errorFromOld error))

theorem parse_success (bytes : Slice U8) (pre : Prefix)
    (h : parseAccepted bytes = ok (.Ok pre)) :
    AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes = ok (.Ok (toOld pre)) := by
  unfold parseAccepted at h
  cases hp : AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes with
  | fail error => simp only [hp, bind_tc_fail] at h; cases h
  | div => simp only [hp, bind_tc_div] at h; cases h
  | ok result =>
    cases result with
    | Err error => simp only [hp, bind_tc_ok] at h; cases h
    | Ok old =>
      simp only [hp, bind_tc_ok] at h
      have he : fromOld old = pre := core.result.Result.Ok.inj (Result.ok.inj h)
      have ho : old = toOld pre := by rw [← he]; rfl
      simpa only [ho] using hp

def completedRecords (pre : Prefix) : List AspisR1.SemanticRecordCodec.Bytes :=
  (pre.records.val.take 25).map (fun frame => frame.val.map AspisR1.ExtractedRecordByteValue.rawByte)

/-- Supplies the strict full25 typed-codec premise from this concrete parser's
actual success. No completed-record equality or chosen decoder witness is a
premise. The outer caller still has to connect its transcript log to these bytes. -/
theorem parse_typedFull (bytes : Slice U8) (pre : Prefix)
    (h : parseAccepted bytes = ok (.Ok pre)) :
    ∃ values : AspisR1.SemanticPrefixCodec.Full,
      AspisR1.SemanticPrefixCodec.decodeFull (completedRecords pre) = some values ∧
      AspisR1.SemanticPrefixCodec.encodeFull values = completedRecords pre ∧
      AspisR1.SemanticPrefixCodec.decodeFrom 0 (completedRecords pre) =
        some (AspisR1.SemanticPrefixCodec.entriesOf values) := by
  simpa only [completedRecords, AspisR1.ExtractedPrefixTypedFull.completedRecords, toOld] using
    AspisR1.ExtractedPrefixTypedFull.parse_decodeFull bytes (toOld pre) (parse_success bytes pre h)

#print axioms toOld_fromOld
#print axioms fromOld_toOld
#print axioms parseAccepted
#print axioms parse_success
#print axioms parse_typedFull
end AspisR1PublicPreparation.PrefixAdapter
