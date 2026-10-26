import AspisR1PrefixAggregateParser.Funs
import AspisR1RecordParser.Funs

/-! Explicit carrier and actual-function agreement between final Prefix-E and
record-parser-F extractions. Shared Rust spans alone are not a Lean cast. -/
namespace AspisR1.ExtractedPrefixFieldAgreement
open Aeneas Aeneas.Std Result

def cmToRecord (x : AspisR1PrefixAggregateParser.field.CM31) :
    AspisR1RecordParser.field.CM31 := ⟨x.a, x.b⟩

def qmToRecord (x : AspisR1PrefixAggregateParser.field.QM31) :
    AspisR1RecordParser.field.QM31 := ⟨cmToRecord x.c0, cmToRecord x.c1⟩

def wideToRecord (x : AspisR1PrefixAggregateParser.field.wide_exact.WideExact) :
    AspisR1RecordParser.field.wide_exact.WideExact :=
  ⟨qmToRecord x.c0, qmToRecord x.c1⟩

def mapResult {α β : Type} (f : α → β) : Result α → Result β
  | ok x => ok (f x)
  | fail e => fail e
  | div => div

theorem mapResult_bind {α β γ : Type} (f : β → γ)
    (m : Result α) (k : α → Result β) :
    mapResult f (m >>= k) = (m >>= fun x => mapResult f (k x)) := by
  cases m <;> rfl

theorem mapResult_ite {α β : Type} (f : α → β)
    (p : Prop) [Decidable p] (a b : Result α) :
    mapResult f (if p then a else b) =
      if p then mapResult f a else mapResult f b := by
  split <;> rfl

@[simp] theorem mapResult_ok {α β : Type} (f : α → β) (x : α) :
    mapResult f (ok x) = ok (f x) := rfl

/-- Same eight limb guards and unchanged coordinate packing, with a fixed map. -/
theorem from_limbs_agreement (limbs : Array U32 8#usize) :
    mapResult (Option.map wideToRecord)
      (AspisR1PrefixAggregateParser.field.wide_exact.WideExact.from_limbs limbs) =
      AspisR1RecordParser.field.wide_exact.WideExact.from_limbs limbs := by
  unfold AspisR1PrefixAggregateParser.field.wide_exact.WideExact.from_limbs
    AspisR1RecordParser.field.wide_exact.WideExact.from_limbs
    AspisR1PrefixAggregateParser.field.P AspisR1RecordParser.field.P
  simp only [mapResult_bind, mapResult_ite, mapResult_ok,
    Option.map_none, Option.map_some]
  rfl

/-- Same byte reads, LE4 assembly, length guard, and mapped constructor. -/
theorem from_le_bytes_agreement (bytes : Slice U8) :
    mapResult (Option.map wideToRecord)
      (AspisR1PrefixAggregateParser.field.wide_exact.WideExact.from_le_bytes bytes) =
      AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes bytes := by
  unfold AspisR1PrefixAggregateParser.field.wide_exact.WideExact.from_le_bytes
    AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes
    AspisR1PrefixAggregateParser.field.wide_exact.WideExact.BYTE_LEN
    AspisR1RecordParser.field.wide_exact.WideExact.BYTE_LEN
  simp only [mapResult_ite, mapResult_bind, mapResult_ok,
    Option.map_none, from_limbs_agreement]

theorem from_le_bytes_success (bytes : Slice U8)
    (w : AspisR1PrefixAggregateParser.field.wide_exact.WideExact)
    (h : AspisR1PrefixAggregateParser.field.wide_exact.WideExact.from_le_bytes bytes =
      ok (some w)) :
    AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes bytes =
      ok (some (wideToRecord w)) := by
  rw [← from_le_bytes_agreement, h]
  rfl

theorem qm_zero_agreement :
    qmToRecord AspisR1PrefixAggregateParser.field.QM31.ZERO =
      AspisR1RecordParser.field.QM31.ZERO := by
  unfold AspisR1PrefixAggregateParser.field.QM31.ZERO
    AspisR1RecordParser.field.QM31.ZERO
  rfl

theorem qm_eq_agreement (x y : AspisR1PrefixAggregateParser.field.QM31) :
    AspisR1PrefixAggregateParser.field.QM31.Insts.CoreCmpPartialEqQM31.eq x y =
      AspisR1RecordParser.field.QM31.Insts.CoreCmpPartialEqQM31.eq
        (qmToRecord x) (qmToRecord y) := by
  rfl

end AspisR1.ExtractedPrefixFieldAgreement

#print axioms AspisR1.ExtractedPrefixFieldAgreement.from_limbs_agreement
#print axioms AspisR1.ExtractedPrefixFieldAgreement.from_le_bytes_agreement
#print axioms AspisR1.ExtractedPrefixFieldAgreement.from_le_bytes_success
#print axioms AspisR1.ExtractedPrefixFieldAgreement.qm_zero_agreement
#print axioms AspisR1.ExtractedPrefixFieldAgreement.qm_eq_agreement
