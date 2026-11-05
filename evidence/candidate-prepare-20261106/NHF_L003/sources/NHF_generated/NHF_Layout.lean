import NFW_StoredWindows
set_option autoImplicit false
namespace AspisR1.NHF_Layout
open Aeneas Aeneas.Std NFW_StoredLayout
/-- Domains of the two compact expansion packets, derived from source offsets. -/
theorem expansion_domains :
 (7031-16=7015) ∧ (7495-7031=464) ∧ (464%16=0) ∧
 (464≤1856) ∧ (928=2*464) ∧ (14759≤32768) := by decide
/-- The original logical split supplies disjoint windows covering the allocation. -/
theorem logical_partition (i : Nat) (inside : i<14759) :
 (i<13831 ∨ (13831≤i ∧ i-13831<928)) := by omega
/-- wide_view reaches no byte beyond openings; full stored length suffices. -/
theorem view_domain (length : Nat) (stored : 57607≤length) :
 7495+32≤length ∧ 7527+224≤length ∧ 7751+32≤length ∧
 7783+224≤length ∧ 8007+2048≤length := by omega
/-- Writes to one compact output cannot hit the other's logical coordinates. -/
theorem split_disjoint (i j : Nat) (left : i<13831) (right : j<928) :
 i≠13831+j := by omega
#print axioms expansion_domains
#print axioms logical_partition
#print axioms view_domain
#print axioms split_disjoint
end AspisR1.NHF_Layout
