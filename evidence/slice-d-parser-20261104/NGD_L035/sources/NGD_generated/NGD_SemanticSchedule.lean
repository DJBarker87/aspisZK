import NFU_PacketDomains
set_option autoImplicit false
namespace NGD_SemanticSchedule
open NFU_PacketDomains
/-- Closed forms for the original 27-row loop, before its five-byte header. -/
def src (r : Nat) : Nat :=
  if r ≤ 2 then 32+5*r else if r ≤ 14 then 64+5*r
  else if r ≤ 25 then 155+453*(r-15) else if r=26 then 6546 else 7015
def dst (r : Nat) : Nat :=
  if r ≤ 2 then 32+5*r else if r ≤ 14 then 64+5*r
  else if r ≤ 25 then 171+901*(r-15) else if r=26 then 12898 else 13831
def stored (r : Nat) : Nat := if 14 ≤ r then payloadSize r / 2 else payloadSize r

theorem start : src 0 = 32 ∧ dst 0 = 32 := by decide
theorem finish : src 27 = 7015 ∧ dst 27 = 13831 := by decide

theorem advance (r : Nat) (live : r < 27) :
    src (r+1) = src r + 5 + stored r ∧
    dst (r+1) = dst r + 5 + payloadSize r := by
  interval_cases r <;> decide

theorem windows (r : Nat) (live : r < 27) :
    src r + 5 + stored r ≤ 7015 ∧ dst r + 5 + payloadSize r ≤ 13831 ∧
    stored r ≤ 1856 ∧ payloadSize r ≤ 3712 := by
  interval_cases r <;> decide

theorem expansion_domain (r : Nat) (low : 14 ≤ r) (live : r < 27) :
    stored r % 16 = 0 ∧ payloadSize r = 2 * stored r := by
  interval_cases r <;> decide

theorem dst_mono (i j : Nat) (order : i ≤ j) (bound : j ≤ 27) : dst i ≤ dst j := by
  unfold dst
  split_ifs <;> omega

theorem src_mono (i j : Nat) (order : i ≤ j) (bound : j ≤ 27) : src i ≤ src j := by
  unfold src
  split_ifs <;> omega

/-- Every write is disjoint from all later row headers and payloads. -/
theorem disjoint (i j : Nat) (order : i < j) (bound : j < 27) :
    dst i + 5 + payloadSize i ≤ dst j := by
  have step := (advance i (by omega)).2
  have mono := dst_mono (i+1) j (by omega) (by omega)
  omega

/-- The final input windows are the same original source allocation ranges. -/
theorem input_disjoint (i j : Nat) (order : i < j) (bound : j < 27) :
    src i + 5 + stored i ≤ src j := by
  have step := (advance i (by omega)).1
  have mono := src_mono (i+1) j (by omega) (by omega)
  omega
#print axioms start
#print axioms finish
#print axioms advance
#print axioms windows
#print axioms expansion_domain
#print axioms dst_mono
#print axioms src_mono
#print axioms disjoint
#print axioms input_disjoint
end NGD_SemanticSchedule
