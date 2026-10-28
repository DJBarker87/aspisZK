import NDF_ReaderRef.Funs
import AspisR1PublicPreparation.Funs
set_option autoImplicit false
namespace NDF_RecordBridge
open Aeneas Aeneas.Std Result

def adapt (r : Result (Option (Slice U8))) :
    Result (core.result.Result (Slice U8) AspisR1PublicPreparation.r1_wire.Error) := do
  let selected ← r
  ok (match selected with | none => .Err .InvalidRow | some bytes => .Ok bytes)

theorem reference (p : AspisR1PublicPreparation.r1_wire.Prefix) (row : U8) :
    adapt (NDF_ReaderRef.record_ref p.records row) =
      AspisR1PublicPreparation.r1_wire.Prefix.record p row := by
  unfold adapt NDF_ReaderRef.record_ref AspisR1PublicPreparation.r1_wire.Prefix.record
  split <;> simp only [lift,bind_tc_ok]
  · rfl
  · simp only [bind_assoc_eq]

#print axioms reference
end NDF_RecordBridge
