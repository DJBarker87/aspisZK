import R1Z.ProverRwDictionaryDomain
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_WireError
open Aeneas Aeneas.Std Result ProverRwFull

deriving instance DecidableEq for r1_wire.Error

/-- Complete derived equality, including payloads on malformed-input errors.
Native comparison is checked separately by the cfg(kani) contract. -/
def equal (a b : r1_wire.Error) : Result Bool :=
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

theorem exact (a b : r1_wire.Error) : equal a b = .ok (decide (a=b)) := by
  cases a <;> cases b <;> simp [equal]

variable [ExternalTypes]
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  { ProverRwDictionaryDomain.selected ops with op256 := equal }

theorem installed (ops : ExternalFuns) (a b : r1_wire.Error) :
    @r1_wire.Error.Insts.CoreCmpPartialEqError.eq _ (selected ops) a b =
      .ok (decide (a=b)) := exact a b

#print axioms exact
#print axioms installed
end R1Z.PDict_WireError
