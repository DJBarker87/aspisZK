import PCI_ValidateField
import PCI_ValidateScan
import PCI_ValidatePrefix
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCI_ValidateComplete
open PCA
open PCI_ValidateField

def scan (one : UInt32) : List UInt32 → Result Bool
  | [] => ok false
  | x::xs => do
    let product ← mul_run one x
    if product != 0 then ok true else scan one xs

theorem scan_result (one : UInt32) (xs : List UInt32) :
    scan one xs=ok (PCI_ValidateScan.run (fun x => PCC.fieldMul one x != 0) xs) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [scan,mul_result,bind_tc_ok,PCI_ValidateScan.run]
    split <;> simp_all

/-- Source-ordered fold of the pinned native windows and CLOSED field calls.
    Every early error is returned before the next call; the scan short-circuits. -/
def source (w : PairWitness) : Result (Except LeafError Unit) := do
  if !PCC.canonical w.firstCommitment || !PCC.canonical w.secondCommitment then
    ok (.error .NonCanonicalCommitment)
  else if w.secondOccupied.toNat>=2147483647 then ok (.error .NonCanonicalOccupancy)
  else if w.secondOccupancyInverse.toNat>=2147483647 then ok (.error .NonCanonicalInverse)
  else
    let oneMinus := PCC.fieldSub 1 w.secondOccupied
    let p0 ← mul_run w.secondOccupied (PCC.fieldSub w.secondOccupied 1)
    if p0 != 0 then ok (.error .OccupancyNotBoolean)
    else
      let p1 ← mul_run w.secondCommitment[7] w.secondOccupancyInverse
      if p1 != w.secondOccupied then ok (.error .SentinelInverseMismatch)
      else
        let p2 ← mul_run oneMinus w.secondOccupancyInverse
        if p2 != 0 then ok (.error .EmptyInverseNonZero)
        else
          let nonzero ← scan oneMinus w.secondCommitment.toList
          if nonzero then ok (.error .EmptyCommitmentNonZero)
          else if w.secondOccupied == 1 && w.secondCommitment[7] == 0 then
            ok (.error .OccupiedSentinelZero)
          else ok (.ok ())

/-- Complete Result at all raw word inputs, with the full error carrier. -/
theorem complete (w : PairWitness) : source w=ok (PCC.validatePair w) := by
  unfold source PCC.validatePair
  simp only [mul_result,scan_result,PCI_ValidateScan.complete,bind_tc_ok,
    PCI_ValidatePrefix.ok_ite]

def observe (w : PairWitness) (state : PCA_State) : Result (Execution Unit) := do
  let out ← source w
  ok ⟨state,[],match out with | .ok () => .ok () | .error e => .error (.leaf e)⟩

theorem result_state_effects (w : PairWitness) (state : PCA_State) :
    observe w state=ok ⟨state,[],match PCC.validatePair w with
      | .ok () => .ok () | .error e => .error (.leaf e)⟩ := by
  simp only [observe,complete,bind_tc_ok]

#print axioms scan_result
#print axioms complete
#print axioms result_state_effects
end PCI_ValidateComplete
