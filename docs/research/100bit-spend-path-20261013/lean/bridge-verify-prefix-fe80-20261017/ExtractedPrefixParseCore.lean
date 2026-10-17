import AspisR1PublicPreparation.Funs
import AspisR1PrefixAggregateParser.Funs

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

#print axioms parseAccepted
#print axioms parse_success
end AspisR1PublicPreparation.PrefixAdapter
