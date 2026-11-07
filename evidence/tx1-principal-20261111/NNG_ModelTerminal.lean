import NNG_InstallBase
import NNG_LIBArrays
import LIB_VTerminal
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_ModelTerminal
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NNG_Transport
open NMP_ResultTransport (outer inner outer_inverse inner_inverse)
open AspisR1.NMT_Transport (arr)
abbrev NativeQ := FIv_NativeArithmetic.NQ
abbrev NativeError := LIB_VTerminal.NativeError
abbrev Error := aspis_core.state_only_prefix.r0.Error

def raiseError : NativeError → Error
 | .Allocation => .Allocation
 | .RowOrder x y => .RowOrder x y
 | .InvalidRow => .InvalidRow
 | .Tag x => .Tag x
 | .Length x => .Length x
 | .NonCanonical x y => .NonCanonical x y
 | .Boundary x => .Boundary x
 | .Terminal => .Terminal
 | .EqualCirclePoints => .EqualCirclePoints
 | .TrailingBytes => .TrailingBytes
 | .Public => .Public

def lowerError : Error → NativeError
 | .Allocation => .Allocation
 | .RowOrder x y => .RowOrder x y
 | .InvalidRow => .InvalidRow
 | .Tag x => .Tag x
 | .Length x => .Length x
 | .NonCanonical x y => .NonCanonical x y
 | .Boundary x => .Boundary x
 | .Terminal => .Terminal
 | .EqualCirclePoints => .EqualCirclePoints
 | .TrailingBytes => .TrailingBytes
 | .Public => .Public

theorem error_roundtrip (e : NativeError) : lowerError (raiseError e) = e := by cases e <;> rfl
#print axioms error_roundtrip

def raiseQ (q : NativeQ) : Q := fromT1 (FIq_Carriers.fromQ q)
def lowerQ (q : Q) : NativeQ := FIq_Carriers.toQ (toT1 q)
theorem q_roundtrip (q : NativeQ) : lowerQ (raiseQ q) = q := by
  unfold lowerQ raiseQ
  rw [fromT1_inverse,FIq_Carriers.nq_roundtrip]
#print axioms q_roundtrip

def native (pub : Public) (claims : Claims) (alpha : Alpha) (orig : aspis_core.state_only_prefix.r0.Challenges) :=
  FIq_Native.pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31
    (FIq_Carriers.toPublic (toT9 pub))
    (FIq_Carriers.mapArray (FIq_Carriers.mapArray lowerQ) claims)
    (FIq_Carriers.mapArray lowerQ alpha)
    (FIq_Carriers.toChallenges (toT3 orig))
def call (pub : Public) (claims : Claims) (alpha : Alpha) (orig : aspis_core.state_only_prefix.r0.Challenges) :=
  outer (inner raiseQ raiseError) (native pub claims alpha orig)

theorem call_model (pub : Public) (claims : Claims) (alpha : Alpha) (orig : aspis_core.state_only_prefix.r0.Challenges) :
    outer (inner lowerQ lowerError) (call pub claims alpha orig) = native pub claims alpha orig := by
  apply outer_inverse
  intro r
  exact inner_inverse raiseQ lowerQ raiseError lowerError q_roundtrip error_roundtrip r
#print axioms call_model
end AspisR1.NNG_ModelTerminal
