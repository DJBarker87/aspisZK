import AspisR1PrefixAggregateParser.Types
open Aeneas Aeneas.Std AspisR1PrefixAggregateParser

namespace AspisR1.PrefixDiscriminantAudit
/-- Constructor-code normal form shared by original and naming-only overlay. -/
theorem constructor_codes (e : r1_wire.Error) :
    r1_wire.Error.read_discriminant e =
      match e with
      | .Allocation => 0#isize
      | .RowOrder _ _ => 1#isize
      | .InvalidRow => 2#isize
      | .Tag _ => 3#isize
      | .Length _ => 4#isize
      | .NonCanonical _ _ => 5#isize
      | .Boundary _ => 6#isize
      | .Terminal => 7#isize
      | .EqualCirclePoints => 8#isize
      | .TrailingBytes => 9#isize
      | .Public => 10#isize := by
  cases e <;> rfl

end AspisR1.PrefixDiscriminantAudit
#print AspisR1PrefixAggregateParser.r1_wire.Error.read_discriminant
#print axioms AspisR1.PrefixDiscriminantAudit.constructor_codes
