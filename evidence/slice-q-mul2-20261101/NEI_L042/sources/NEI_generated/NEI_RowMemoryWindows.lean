import KMX_CopyMeaning
set_option autoImplicit false
namespace NEI_RowMemoryWindows
/-- Every observed byte of a different native U64[4] row is disjoint from the
selected row's 32-byte copy/write interval. Allocation interpretation is external. -/
theorem disjoint (selected observed byte : Nat) (different : observed ≠ selected)
 (within : byte<32) :
 observed*32+byte < selected*32 ∨ selected*32+32 ≤ observed*32+byte := by omega

/-- Frame composition over the exact KMX copy value law, not a copy stub. -/
theorem row_frame {α : Type} (src dst : Nat → α) (selected observed byte : Nat)
 (different : observed ≠ selected) (within : byte<32) :
 KMX_CopyMeaning.loop src dst (selected*32) 32 (observed*32+byte)=dst (observed*32+byte) :=
 KMX_CopyMeaning.copy_frame src dst _ _ _ (disjoint selected observed byte different within)

theorem selected_row {α : Type} (src dst : Nat → α) (selected byte : Nat) (within : byte<32) :
 KMX_CopyMeaning.loop src dst (selected*32) 32 (selected*32+byte)=src (selected*32+byte) := by
 rw [KMX_CopyMeaning.loop_spec,if_pos]
 omega
#print axioms disjoint
#print axioms row_frame
#print axioms selected_row
end NEI_RowMemoryWindows
