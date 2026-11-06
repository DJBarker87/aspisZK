import NLA_LaneAssemble
set_option autoImplicit false
namespace NLK_LaneGeometry
/-- Complete original-buffer geometry for every digest call in217. -/
theorem frontier (level byte : Nat) (hl : level<20) (hb : byte<32) :
  80+(48+32*level+byte)=128+32*level+byte ∧
  128+32*level+byte<768 ∧ 128+32*level+32≤768 := by omega

theorem root_disjoint (level rootByte frontierByte : Nat)
    (hr : rootByte<32) (hf : frontierByte<32) :
    96+rootByte ≠ 128+32*level+frontierByte := by omega

theorem header_disjoint (level byte headerByte : Nat)
    (hh : headerByte<80) : headerByte ≠ 128+32*level+byte := by omega

/-- A rejected oversized length cannot reach a source slice. No finite
allocation bound is introduced by the768-byte native backing array. -/
theorem wrong_length (length : Nat) (large : 768<length) : length≠768 := by omega

#print axioms frontier
#print axioms root_disjoint
#print axioms header_disjoint
#print axioms wrong_length
end NLK_LaneGeometry
