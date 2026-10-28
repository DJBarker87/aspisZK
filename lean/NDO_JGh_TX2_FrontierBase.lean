import NDO_JGh_TX2_NodeViews
import NDO_JGc_TX2_M2Layout
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGh_TX2_Frontiers
open OraclePortSelectedDraft OracleDecisionMultiBuild
theorem unoccupied (is : List Nat) (h b : Nat) (no : ¬Occupied is h b) : OraclePortSelectedDraft.frontier is h b=[(h,b)] := by
  cases h <;> simp only [OraclePortSelectedDraft.frontier,if_neg no]
#print axioms unoccupied
def coords0_000 : List (Nat×Nat) := []
theorem front0_000 : OraclePortSelectedDraft.frontier JGf_TX2_M0Roots.indices 0 132355=coords0_000 := by
  rw [OraclePortSelectedDraft.frontier,if_pos (by decide : Occupied JGf_TX2_M0Roots.indices 0 132355)]
  rfl
#print axioms front0_000
def coords0_001 : List (Nat×Nat) := []
theorem front0_001 : OraclePortSelectedDraft.frontier JGf_TX2_M0Roots.indices 0 218094=coords0_001 := by
  rw [OraclePortSelectedDraft.frontier,if_pos (by decide : Occupied JGf_TX2_M0Roots.indices 0 218094)]
  rfl
#print axioms front0_001
def coords0_002 : List (Nat×Nat) := []
theorem front0_002 : OraclePortSelectedDraft.frontier JGf_TX2_M0Roots.indices 0 178080=coords0_002 := by
  rw [OraclePortSelectedDraft.frontier,if_pos (by decide : Occupied JGf_TX2_M0Roots.indices 0 178080)]
  rfl
#print axioms front0_002
def coords0_003 : List (Nat×Nat) := []
theorem front0_003 : OraclePortSelectedDraft.frontier JGf_TX2_M0Roots.indices 0 149624=coords0_003 := by
  rw [OraclePortSelectedDraft.frontier,if_pos (by decide : Occupied JGf_TX2_M0Roots.indices 0 149624)]
  rfl
#print axioms front0_003
def coords0_004 : List (Nat×Nat) := []
theorem front0_004 : OraclePortSelectedDraft.frontier JGf_TX2_M0Roots.indices 0 166165=coords0_004 := by
  rw [OraclePortSelectedDraft.frontier,if_pos (by decide : Occupied JGf_TX2_M0Roots.indices 0 166165)]
  rfl
#print axioms front0_004
def coords0_005 : List (Nat×Nat) := []
theorem front0_005 : OraclePortSelectedDraft.frontier JGf_TX2_M0Roots.indices 0 42158=coords0_005 := by
  rw [OraclePortSelectedDraft.frontier,if_pos (by decide : Occupied JGf_TX2_M0Roots.indices 0 42158)]
  rfl
#print axioms front0_005
def coords0_006 : List (Nat×Nat) := []
theorem front0_006 : OraclePortSelectedDraft.frontier JGf_TX2_M0Roots.indices 0 179622=coords0_006 := by
  rw [OraclePortSelectedDraft.frontier,if_pos (by decide : Occupied JGf_TX2_M0Roots.indices 0 179622)]
  rfl
#print axioms front0_006
def coords0_007 : List (Nat×Nat) := []
theorem front0_007 : OraclePortSelectedDraft.frontier JGf_TX2_M0Roots.indices 0 21248=coords0_007 := by
  rw [OraclePortSelectedDraft.frontier,if_pos (by decide : Occupied JGf_TX2_M0Roots.indices 0 21248)]
  rfl
#print axioms front0_007
def coords0_008 : List (Nat×Nat) := []
theorem front0_008 : OraclePortSelectedDraft.frontier JGf_TX2_M0Roots.indices 0 63860=coords0_008 := by
  rw [OraclePortSelectedDraft.frontier,if_pos (by decide : Occupied JGf_TX2_M0Roots.indices 0 63860)]
  rfl
#print axioms front0_008
def coords0_009 : List (Nat×Nat) := []
theorem front0_009 : OraclePortSelectedDraft.frontier JGf_TX2_M0Roots.indices 0 55377=coords0_009 := by
  rw [OraclePortSelectedDraft.frontier,if_pos (by decide : Occupied JGf_TX2_M0Roots.indices 0 55377)]
  rfl
#print axioms front0_009
def coords0_010 : List (Nat×Nat) := []
theorem front0_010 : OraclePortSelectedDraft.frontier JGf_TX2_M0Roots.indices 0 185637=coords0_010 := by
  rw [OraclePortSelectedDraft.frontier,if_pos (by decide : Occupied JGf_TX2_M0Roots.indices 0 185637)]
  rfl
#print axioms front0_010
def coords0_011 : List (Nat×Nat) := []
theorem front0_011 : OraclePortSelectedDraft.frontier JGf_TX2_M0Roots.indices 0 14297=coords0_011 := by
  rw [OraclePortSelectedDraft.frontier,if_pos (by decide : Occupied JGf_TX2_M0Roots.indices 0 14297)]
  rfl
#print axioms front0_011
def coords2_000 : List (Nat×Nat) := []
theorem front2_000 : OraclePortSelectedDraft.frontier JGc_TX2_M2Roots.indices 0 33088=coords2_000 := by
  rw [OraclePortSelectedDraft.frontier,if_pos (by decide : Occupied JGc_TX2_M2Roots.indices 0 33088)]
  rfl
#print axioms front2_000
def coords2_001 : List (Nat×Nat) := []
theorem front2_001 : OraclePortSelectedDraft.frontier JGc_TX2_M2Roots.indices 0 54523=coords2_001 := by
  rw [OraclePortSelectedDraft.frontier,if_pos (by decide : Occupied JGc_TX2_M2Roots.indices 0 54523)]
  rfl
#print axioms front2_001
def coords2_002 : List (Nat×Nat) := []
theorem front2_002 : OraclePortSelectedDraft.frontier JGc_TX2_M2Roots.indices 0 44520=coords2_002 := by
  rw [OraclePortSelectedDraft.frontier,if_pos (by decide : Occupied JGc_TX2_M2Roots.indices 0 44520)]
  rfl
#print axioms front2_002
def coords2_003 : List (Nat×Nat) := []
theorem front2_003 : OraclePortSelectedDraft.frontier JGc_TX2_M2Roots.indices 0 37406=coords2_003 := by
  rw [OraclePortSelectedDraft.frontier,if_pos (by decide : Occupied JGc_TX2_M2Roots.indices 0 37406)]
  rfl
#print axioms front2_003
def coords2_004 : List (Nat×Nat) := []
theorem front2_004 : OraclePortSelectedDraft.frontier JGc_TX2_M2Roots.indices 0 41541=coords2_004 := by
  rw [OraclePortSelectedDraft.frontier,if_pos (by decide : Occupied JGc_TX2_M2Roots.indices 0 41541)]
  rfl
#print axioms front2_004
def coords2_005 : List (Nat×Nat) := []
theorem front2_005 : OraclePortSelectedDraft.frontier JGc_TX2_M2Roots.indices 0 10539=coords2_005 := by
  rw [OraclePortSelectedDraft.frontier,if_pos (by decide : Occupied JGc_TX2_M2Roots.indices 0 10539)]
  rfl
#print axioms front2_005
def coords2_006 : List (Nat×Nat) := []
theorem front2_006 : OraclePortSelectedDraft.frontier JGc_TX2_M2Roots.indices 0 44905=coords2_006 := by
  rw [OraclePortSelectedDraft.frontier,if_pos (by decide : Occupied JGc_TX2_M2Roots.indices 0 44905)]
  rfl
#print axioms front2_006
def coords2_007 : List (Nat×Nat) := []
theorem front2_007 : OraclePortSelectedDraft.frontier JGc_TX2_M2Roots.indices 0 5312=coords2_007 := by
  rw [OraclePortSelectedDraft.frontier,if_pos (by decide : Occupied JGc_TX2_M2Roots.indices 0 5312)]
  rfl
#print axioms front2_007
def coords2_008 : List (Nat×Nat) := []
theorem front2_008 : OraclePortSelectedDraft.frontier JGc_TX2_M2Roots.indices 0 15965=coords2_008 := by
  rw [OraclePortSelectedDraft.frontier,if_pos (by decide : Occupied JGc_TX2_M2Roots.indices 0 15965)]
  rfl
#print axioms front2_008
def coords2_009 : List (Nat×Nat) := []
theorem front2_009 : OraclePortSelectedDraft.frontier JGc_TX2_M2Roots.indices 0 13844=coords2_009 := by
  rw [OraclePortSelectedDraft.frontier,if_pos (by decide : Occupied JGc_TX2_M2Roots.indices 0 13844)]
  rfl
#print axioms front2_009
def coords2_010 : List (Nat×Nat) := []
theorem front2_010 : OraclePortSelectedDraft.frontier JGc_TX2_M2Roots.indices 0 46409=coords2_010 := by
  rw [OraclePortSelectedDraft.frontier,if_pos (by decide : Occupied JGc_TX2_M2Roots.indices 0 46409)]
  rfl
#print axioms front2_010
def coords2_011 : List (Nat×Nat) := []
theorem front2_011 : OraclePortSelectedDraft.frontier JGc_TX2_M2Roots.indices 0 3574=coords2_011 := by
  rw [OraclePortSelectedDraft.frontier,if_pos (by decide : Occupied JGc_TX2_M2Roots.indices 0 3574)]
  rfl
#print axioms front2_011
end AspisR1.JGh_TX2_Frontiers
end
