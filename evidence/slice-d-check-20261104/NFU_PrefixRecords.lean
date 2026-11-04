import NFU_RecordGetters
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NFU_PrefixRecords
open AspisR1PublicPreparation

def selected (p : r1_wire.Prefix) (row : U8) :
    Result (core.result.Result (Slice U8) r1_wire.Error) := do
  if row >= 27#u8 then ok (.Err .InvalidRow)
  else
    let i ← lift (UScalar.cast .Usize row)
    let bytes ← Array.index_usize p.records i
    ok (.Ok bytes)

theorem record (p : r1_wire.Prefix) (row : U8) :
    r1_wire.Prefix.record p row = selected p row := by rfl

def token (row : U8) (reply : Result (core.result.Result (Slice U8) r1_wire.Error)) :
    Result (core.result.Result r1_wire.ValidatedRecord r1_wire.Error) := do
  let outcome ← reply
  ok (match outcome with
    | .Ok bytes => .Ok { row, framed := bytes }
    | .Err error => .Err error)

/-- Substitution uses the SAME selected reply, preserving every error and the
original row/slice. No independent token or accepted parser result is assumed. -/
theorem validated_record (p : r1_wire.Prefix) (row : U8) :
    r1_wire.Prefix.validated_record p row = token row (selected p row) := by
  rw [← record]
  unfold r1_wire.Prefix.validated_record token
  cases h : r1_wire.Prefix.record p row <;> simp only [h, bind_tc_fail, bind_tc_div, bind_tc_ok]
  rename_i outcome
  cases outcome <;> rfl
#print axioms record
#print axioms validated_record
end NFU_PrefixRecords
