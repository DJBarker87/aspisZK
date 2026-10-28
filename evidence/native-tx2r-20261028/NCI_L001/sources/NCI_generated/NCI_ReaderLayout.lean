import Init
set_option autoImplicit false
namespace AspisR1.NCI_ReaderLayout
-- Cursor arithmetic for the S2 checkpoint. No byte decoder is postulated here.
def widths : List Nat := [32,32,32,32,32,32,32,16,88,160,64,32,32,16,1024]
def ends : List Nat := [112,144,176,208,240,272,304,320,408,568,632,664,696,712,1736]
theorem body_end : 80 + widths.sum = 1736 := by decide
theorem checksum_end : 1736 + 32 = 1768 := by decide
theorem weight_read_bound (i : Nat) (hi : i < 64) :
    712 + 16*i + 16 ≤ 1736 := by omega
theorem semantic_read_bound (i : Nat) (hi : i < 10) :
    408 + 16*i + 16 ≤ 568 := by omega
theorem query_read_bound (i : Nat) (hi : i < 22) :
    320 + 4*i + 4 ≤ 408 := by omega
theorem bounded_raw (at n : Nat) (h : at+n ≤ 1736) : at+n ≤ 1768 := by omega
#print axioms body_end
#print axioms checksum_end
#print axioms weight_read_bound
#print axioms semantic_read_bound
#print axioms query_read_bound
#print axioms bounded_raw
end AspisR1.NCI_ReaderLayout
