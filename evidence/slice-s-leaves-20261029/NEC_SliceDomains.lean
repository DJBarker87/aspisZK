import Aeneas
set_option autoImplicit false
namespace NEC_SliceDomains

/-- Geometry facts establish only caller widths; they do not assume a parser
accepted, an input digest was canonical, or a child returned success. -/
theorem terminal_payment {α : Type} (bytes : List α) (length : bytes.length=1880) :
 (bytes.drop 1664).length=216 := by simp [List.length_drop,length]

theorem request_payment {α : Type} (bytes : List α) (length : bytes.length=320) :
 (bytes.drop 104).length=216 := by simp [List.length_drop,length]

theorem terminal_lane {α : Type} (bytes : List α) (length : bytes.length=1880) :
 ((bytes.drop 144).take 1520).length=1520 := by simp [List.length_take,List.length_drop,length]

theorem terminal_anchor {α : Type} (bytes : List α) (length : bytes.length=1880) :
 ((bytes.drop 112).take 32).length=32 := by simp [List.length_take,List.length_drop,length]

theorem live_child {α : Type} (bytes : List α) (length : bytes.length=1520) :
 ((bytes.drop 32).take 800).length=800 := by simp [List.length_take,List.length_drop,length]

theorem after_child {α : Type} (bytes : List α) (length : bytes.length=1520) :
 (bytes.drop 832).length=688 := by simp [List.length_drop,length]

theorem terminal_common_minimum (length : Nat) (caller : length=1880) : 1664≤length := by omega

theorem result_after {α : Type} (bytes : List α) (length : bytes.length=792) :
 (bytes.drop 104).length=688 := by simp [List.length_drop,length]

theorem scan_candidate {α : Type} (bytes : List α) (proofLength : Nat)
 (length : bytes.length=688+proofLength) : (bytes.take 688).length=688 := by
 simp only [List.length_take,length]
 omega

theorem scan_proof {α : Type} (bytes : List α) (proofLength : Nat)
 (length : bytes.length=688+proofLength) : (bytes.drop 688).length=proofLength := by
 simp only [List.length_drop,length]
 omega

theorem scan_tag (proofLength : Nat) (hasTag : 8<proofLength) : 688+8<688+proofLength := by omega

theorem live_scalar_disjoint : 112+8≤120 ∧ 120+8≤128 ∧ 128+32≤160 := by omega

theorem common_payment_disjoint : 112+32≤144 ∧ 144+1520≤1664 ∧ 1664+216=1880 := by omega

#print axioms terminal_payment
#print axioms request_payment
#print axioms terminal_lane
#print axioms terminal_anchor
#print axioms live_child
#print axioms after_child
#print axioms terminal_common_minimum
#print axioms result_after
#print axioms scan_candidate
#print axioms scan_proof
#print axioms scan_tag
#print axioms live_scalar_disjoint
#print axioms common_payment_disjoint
end NEC_SliceDomains
