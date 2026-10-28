import NBI_CountScan

set_option autoImplicit false
namespace AspisR1.NBI_CountPort
open MultiproofConeLiveOrder
attribute [local instance] Classical.propDecidable

/-- Equal-parent scanning and the installed paired-child count-row advance
have identical cursors and contributions on the native unread-order domain. -/
theorem scan_row (key : Nat → Nat) (n i : Nat) (active : i < n)
    (ordered : Strict key i n) :
    NBI_CountScan.scan key (key i/2) n (n-i) i = advance key n i ∧
    2-(NBI_CountScan.scan key (key i/2) n (n-i) i-i) =
      (if pairAt key n i then 0 else 1) := by
  have pair : (i+1 < n ∧ key (i+1)/2 = key i/2) ↔ pairAt key n i := by
    constructor
    · rintro ⟨next,same⟩
      exact ⟨next,(MultiproofConeCountGroups.same_parent (key i) (key (i+1))
        (ordered i (i+1) (by omega) (by omega) next)).mp same.symm⟩
    · rintro ⟨next,paired⟩
      exact ⟨next,((MultiproofConeCountGroups.same_parent (key i) (key (i+1))
        (ordered i (i+1) (by omega) (by omega) next)).mpr paired).symm⟩
  have result := (NBI_CountScan.scan_group key n i active ordered).1
  have endpoint : NBI_CountScan.scan key (key i/2) n (n-i) i = advance key n i := by
    rw [result,advance,propext pair]
  refine ⟨endpoint,?_⟩
  rw [endpoint,advance]
  split <;> omega

#print axioms scan_row
end AspisR1.NBI_CountPort
