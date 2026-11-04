import AspisR1PublicPreparation.Funs
import AspisR1PrefixAggregateParser.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NFU_RecordGetters
/-- Complete emitted scalar return; no validation premise is needed by the getter. -/
theorem row (record : AspisR1PublicPreparation.r1_wire.ValidatedRecord) :
    AspisR1PublicPreparation.r1_wire.ValidatedRecord.impl.row record = ok record.row := by
  rfl
/-- The returned slice is the original record slice, with its complete value. -/
theorem framed (record : AspisR1PublicPreparation.r1_wire.ValidatedRecord) :
    AspisR1PublicPreparation.r1_wire.ValidatedRecord.impl.framed record = ok record.framed := by
  rfl
/-- Parser-owned token has the identical projection law. -/
theorem parser_row (record : AspisR1PrefixAggregateParser.r1_wire.ValidatedRecord) :
    AspisR1PrefixAggregateParser.r1_wire.ValidatedRecord.impl.row record = ok record.row := by
  rfl
theorem parser_framed (record : AspisR1PrefixAggregateParser.r1_wire.ValidatedRecord) :
    AspisR1PrefixAggregateParser.r1_wire.ValidatedRecord.impl.framed record = ok record.framed := by
  rfl
/-- Transport explicitly preserves both fields; no second independently chosen token. -/
def port (record : AspisR1PublicPreparation.r1_wire.ValidatedRecord) :
    AspisR1PrefixAggregateParser.r1_wire.ValidatedRecord :=
  { row := record.row, framed := record.framed }
theorem same_token (record : AspisR1PublicPreparation.r1_wire.ValidatedRecord) :
    (port record).row = record.row ∧ (port record).framed = record.framed := by
  exact ⟨rfl, rfl⟩
#print axioms row
#print axioms framed
#print axioms parser_row
#print axioms parser_framed
#print axioms same_token
end NFU_RecordGetters
