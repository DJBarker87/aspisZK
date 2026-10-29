import PV_DIAG2_Rejection
set_option autoImplicit false
noncomputable section
namespace PV_DIAG2
open Aeneas Aeneas.Std Result ProverRwFull
local instance : DecidableEq r1_wire.Error := Classical.decEq _
def wireEqual (a b : r1_wire.Error) : Result Bool :=
  .ok (match a,b with
  | .Allocation,.Allocation => true
  | .RowOrder a b,.RowOrder c d => decide (a=c ∧ b=d)
  | .InvalidRow,.InvalidRow => true
  | .Tag a,.Tag b => decide (a=b)
  | .Length a,.Length b => decide (a=b)
  | .NonCanonical a b,.NonCanonical c d => decide (a=c ∧ b=d)
  | .Boundary a,.Boundary b => decide (a=b)
  | .Terminal,.Terminal => true
  | .EqualCirclePoints,.EqualCirclePoints => true
  | .TrailingBytes,.TrailingBytes => true
  | .Public,.Public => true
  | .ActivePole,.ActivePole => true
  | _,_ => false)

theorem wire_equal_exact (a b : r1_wire.Error) : wireEqual a b = .ok (decide (a=b)) := by
  cases a <;> cases b <;> simp [wireEqual]


/-- Explicit equality dictionary, not an assumption about arbitrary op256. -/
def withWireEquality [ExternalTypes] (ops : ExternalFuns) : ExternalFuns :=
 {ops with op256 := wireEqual}

theorem active_pole_installed [ExternalTypes] (ops : ExternalFuns) :
 @prover.semantic_error _ (withWireEquality ops) .ActivePole = ok .Rejected := by
 apply active_pole_rejected
 rfl

#print axioms wire_equal_exact
#print axioms active_pole_installed
end PV_DIAG2
