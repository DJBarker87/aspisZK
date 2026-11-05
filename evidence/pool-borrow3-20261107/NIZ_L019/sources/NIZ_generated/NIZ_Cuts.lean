import NIZ_KeyEquality
import NIZ_Dominance
set_option autoImplicit false
namespace NIZ_Cuts

/-- K006: exactly the asserted zero observation and ONE arbitrary observed byte.
No sign/magnitude, whole heap identity or SDK-counter relation is inserted. -/
def comparison (before after : Nat → UInt8) (left right observer : Nat)
    (reply : Int) : Prop :=
  (reply = 0 ↔ before left = before right) ∧ after observer = before observer

/-- K017/K019: actual capture-free callback reply and observed-byte frame. -/
def noop (before after : UInt8) (returnedOk : Bool) : Prop :=
  returnedOk = true ∧ after = before

/-- K021: fixed native key size, readable byte-view length and selected value. -/
def keyView (input view : Nat → UInt8) (index nativeSize length : Nat) : Prop :=
  nativeSize = 32 ∧ length = 32 ∧ view index = input index

/-- K023, conditional on the NIZ_eq value/source pairing in NIZ_STUBS.md. -/
def prefixPredicate (left right : Nat → Nat) (found : Bool) : Prop :=
  found = NIZ_KeyEquality.same left right 0 32

/-- K028: only the original unit/InvalidArgument Result arms are admitted.
The Boolean is the explicit constructor tag, not an observer/function pointer. -/
def questionmark (replyOk reached returnedOk : Bool) : Prop :=
  reached = replyOk ∧ returnedOk = replyOk

/-- K011..K016/K030..K037 use NIZ_Dominance.EdgeCut verbatim. Its arguments
are exact MIR edge labels; it says nothing about SDK pointer/guard identity. -/
abbrev cfg {V : Type} := @NIZ_Dominance.EdgeCut V
end NIZ_Cuts
