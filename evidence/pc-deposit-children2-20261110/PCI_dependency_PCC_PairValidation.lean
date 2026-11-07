import PCC_DepositDecodeReference
set_option autoImplicit false
namespace PCC
open PCA
/-- Natural specs only. Native multiplication requires the existing
Lean-discharged field stubs, never a Kani multiplication proof. -/
def fieldMul (a b : UInt32) : UInt32 :=
  UInt32.ofNat ((a.toNat * b.toNat) % 2147483647)
def fieldSub (a b : UInt32) : UInt32 :=
  UInt32.ofNat ((a.toNat + 2147483647 - b.toNat) % 2147483647)

def validatePair (w : PairWitness) : Except LeafError Unit :=
  if !canonical w.firstCommitment || !canonical w.secondCommitment then .error .NonCanonicalCommitment
  else if w.secondOccupied.toNat >= 2147483647 then .error .NonCanonicalOccupancy
  else if w.secondOccupancyInverse.toNat >= 2147483647 then .error .NonCanonicalInverse
  else
    let oneMinus := fieldSub 1 w.secondOccupied
    if fieldMul w.secondOccupied (fieldSub w.secondOccupied 1) != 0 then .error .OccupancyNotBoolean
    else if fieldMul w.secondCommitment[7] w.secondOccupancyInverse != w.secondOccupied then
      .error .SentinelInverseMismatch
    else if fieldMul oneMinus w.secondOccupancyInverse != 0 then .error .EmptyInverseNonZero
    else if w.secondCommitment.toList.any (fun limb => fieldMul oneMinus limb != 0) then
      .error .EmptyCommitmentNonZero
    else if w.secondOccupied == 1 && w.secondCommitment[7] == 0 then .error .OccupiedSentinelZero
    else .ok ()
end PCC
