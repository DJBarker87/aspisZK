import NGD_AtG.Types
import AspisR1PrefixAggregateParser.Types
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGD_ErrorPort
abbrev Wire := AspisR1PrefixAggregateParser.r1_wire.Error
def toWire : NGD_AtG.Error → Wire
  | .Allocation => .Allocation
  | .RowOrder a b => .RowOrder a b
  | .InvalidRow => .InvalidRow
  | .Tag r => .Tag r
  | .Length r => .Length r
  | .NonCanonical r i => .NonCanonical r i
  | .Boundary r => .Boundary r
  | .Terminal => .Terminal
  | .EqualCirclePoints => .EqualCirclePoints
  | .TrailingBytes => .TrailingBytes
  | .Public => .Public
def fromWire : Wire → NGD_AtG.Error
  | .Allocation => .Allocation
  | .RowOrder a b => .RowOrder a b
  | .InvalidRow => .InvalidRow
  | .Tag r => .Tag r
  | .Length r => .Length r
  | .NonCanonical r i => .NonCanonical r i
  | .Boundary r => .Boundary r
  | .Terminal => .Terminal
  | .EqualCirclePoints => .EqualCirclePoints
  | .TrailingBytes => .TrailingBytes
  | .Public => .Public
theorem to_from (e : Wire) : toWire (fromWire e) = e := by cases e <;> rfl
theorem from_to (e : NGD_AtG.Error) : fromWire (toWire e) = e := by cases e <;> rfl
def mapError {α : Type} : core.result.Result α NGD_AtG.Error → core.result.Result α Wire
  | .Ok x => .Ok x
  | .Err e => .Err (toWire e)
def unmapError {α : Type} : core.result.Result α Wire → core.result.Result α NGD_AtG.Error
  | .Ok x => .Ok x
  | .Err e => .Err (fromWire e)
theorem result_roundtrip {α : Type} (r : core.result.Result α Wire) :
    mapError (unmapError r) = r := by cases r <;> simp [mapError,unmapError,to_from]
#print axioms to_from
#print axioms from_to
#print axioms result_roundtrip
end NGD_ErrorPort
