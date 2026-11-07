import PV_THR2_PacketJoinedHandlerAway
import PV_THR2_PacketJoinedTable
set_option autoImplicit false
namespace PV_THR2_JoinedCertDescriptor
open PV_STX2_Syntax PV_STX2_SliceMachine
/-- Shape test, not a source value test. The generic BoxNew token is native. -/
def isBox : Data → Bool
  | .object [("Regular",.object [("kind",.object [("Fun",.object [("Builtin",.atom "BoxNew")])]),("generics",_)])] => true
  | _ => false
/-- Additional joined dispositions;121 is already a retained scope child and
is deliberately not excluded. These are internal generated syntax facts. -/
def Extra (fn : Data) : Prop :=
  PV_THR2_OffPath.functionId fn ≠ some 216 ∧
  PV_THR2_OffPath.functionId fn ≠ some 218 ∧
  PV_THR2_OffPath.functionId fn ≠ some 315 ∧
  PV_THR2_OffPath.functionId fn ≠ some 217 ∧
  PV_THR2_OffPath.functionId fn ≠ some 312 ∧
  PV_THR2_OffPath.functionId fn ≠ some 313 ∧
  PV_THR2_OffPath.functionId fn ≠ some 320 ∧ isBox fn = false
abbrev IdSafe (fn : Data) := PV_THR2_OffPath.functionId fn ≠ some 222 ∧ Extra fn
abbrev Third (fn other : Data) := fn ≠ other ∧ Extra fn
/-- Finite trace property, never a closure hypothesis. -/
def Clear {W E : Type} (q : PV_THR2_IntrinsicState.State W E) : Prop :=
  ∀ c, q.current.status = .running c → ∀ wait fn a args,
    c.frame.waiting = some wait →
    wait.request = .child fn a args →
    fn ≠ PV_THR2_Source361PacketChildren.fn58 ∧
    fn ≠ PV_THR2_PacketDataTable.fn126 ∧ Third fn PV_THR2_PacketDataTable.fn222
/-- The generated syntax exclusions imply complete joined-handler agreement.
All five native semantics tokens are identified by their emitted shapes. -/
theorem native (fn : Data) (extra : Extra fn) :
    PV_THR2_PacketJoinedHandlerAway.Other fn := by
  rcases extra with ⟨n216,n218,n315,n217,n312,n313,n320,box⟩
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro eq
    rw [eq] at box
    cases box
  · intro eq; exact n217 (congrArg PV_THR2_OffPath.functionId eq)
  · intro eq; exact n312 (congrArg PV_THR2_OffPath.functionId eq)
  · intro eq; exact n313 (congrArg PV_THR2_OffPath.functionId eq)
  · intro eq; exact n320 (congrArg PV_THR2_OffPath.functionId eq)
#print axioms native
#print axioms isBox
#print axioms Extra
#print axioms IdSafe
#print axioms Third
#print axioms Clear
end PV_THR2_JoinedCertDescriptor
infix:50 " ≠ⱼ " => PV_THR2_JoinedCertDescriptor.Third
