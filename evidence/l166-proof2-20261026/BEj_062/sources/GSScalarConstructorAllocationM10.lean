import RecoveryParserAllocationM10
import GSScalarTraceFieldWorkM10

/-! Source-operand primitive constructor tariffs. Raw gcd/division and
binaryRec multiply/remainder schedules already count coefficient construction
steps on the actual operands. Each such scalar/slot step is a fixed-width
constructor group. Explicit degree-capped trim, normalization and scheduler
result groups are added at the primitive call sites. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.GSScalarConstructorAllocationM10
open CompPoly GSScalarCallScheduleM10 RawExtractorCostLedger
variable {K : Type} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K] [Fintype K]

def normalizationCells (D : Nat) : Nat := 10*(2*(D+1)+1)^2

def callCells (D : Nat) : Call K → Nat
  | .gcd a b => gcdCharge (a.val,b.val)+normalizationCells D+1
  | .division a b => CompPolyFactorRawDivisionBridge.actualDivisionCharge a b+normalizationCells D+1
  | .power a m e => (GSBinaryModPowerFieldWorkM10.eval a m e).2+(e+1)*normalizationCells D+1

theorem normalization_paid (D : Nat) : normalizationCells D+1 ≤ GSScalarTraceFieldWorkM10.normalization D := by
  have hp : 1 ≤ (2*(D+1)+1)^2 := by
    have h := Nat.pow_le_pow_left (show 1 ≤ 2*(D+1)+1 by omega) 2
    simpa only [one_pow] using h
  unfold normalizationCells GSScalarTraceFieldWorkM10.normalization
  omega

theorem call_paid (D : Nat) (c : Call K) : callCells D c ≤ GSScalarTraceFieldWorkM10.callWork D c := by
  have hn := normalization_paid D
  cases c with
  | gcd a b => change _+_+1 ≤ _+_; omega
  | division a b => change _+_+1 ≤ _+_; omega
  | power a m e =>
    have hh := Nat.mul_le_mul_left (e+1) hn
    change _+(e+1)*normalizationCells D+1 ≤ _+(e+1)*GSScalarTraceFieldWorkM10.normalization D
    nlinarith

def traceCells (D : Nat) (cs : List (Call K)) : Nat := (cs.map (callCells D)).sum

theorem trace_paid (D : Nat) (cs : List (Call K)) :
    traceCells D cs ≤ GSScalarTraceFieldWorkM10.traceWork D cs :=
  RecoveryParserAllocationM10.sum_mono cs _ _ (fun c _ => call_paid D c)

#print axioms normalization_paid
#print axioms call_paid
#print axioms trace_paid
end AspisR1.GSScalarConstructorAllocationM10
end
