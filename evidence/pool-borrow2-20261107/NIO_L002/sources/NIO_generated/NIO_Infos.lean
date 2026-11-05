import NIO_Cpi
set_option autoImplicit false
namespace NIO_Infos

def depositPos (j : Nat) : Nat :=
  if j = 0 then 1 else if j = 1 then 0 else if j = 2 then 3 else if j = 3 then 2 else 4

def withdrawalPos (j : Nat) : Nat :=
  if j = 0 then 1 else if j = 1 then 0 else j

theorem depositPos_bound (j : Nat) : depositPos j < 5 := by
  unfold depositPos
  split <;> (try omega)
  split <;> (try omega)
  split <;> (try omega)
  split <;> omega
#print axioms depositPos_bound

theorem withdrawalPos_bound (j : Nat) (h : j < 5) : withdrawalPos j < 5 := by
  unfold withdrawalPos
  split <;> (try omega)
  split <;> omega
#print axioms withdrawalPos_bound

/-- The actual source uniqueness check is bounded by the supplied account list. -/
def UniqueKeys (key : Nat → Nat) (len : Nat) : Prop :=
  ∀ i j, i < len → j < len → i ≠ j → key i ≠ key j

theorem deposit_key_exclusion (key : Nat → Nat) (len start guarded j : Nat)
    (unique : UniqueKeys key len) (gBound : guarded < len)
    (tokenBound : start + 5 ≤ len)
    (startMode : start = 3 ∨ start = 4)
    (guardMode : guarded = 1 ∨ guarded = 2 ∨ (start = 4 ∧ guarded = 3)) :
    key guarded ≠ key (start + depositPos j) := by
  apply unique guarded (start + depositPos j) gBound
  · have := depositPos_bound j
    omega
  · exact NIO_Cpi.deposit_index_separation start guarded (depositPos j) startMode guardMode
#print axioms deposit_key_exclusion

theorem forest_key_exclusion (key : Nat → Nat) (len cursor guarded j : Nat)
    (unique : UniqueKeys key len) (gBound : guarded < len)
    (tokenBound : cursor + 7 + 5 ≤ len) (jBound : j < 5)
    (guardMode : guarded = 2 ∨ guarded = 3 ∨ guarded = 4 ∨ guarded = cursor)
    (cursorBound : 4 ≤ cursor) :
    key guarded ≠ key (cursor + 7 + withdrawalPos j) := by
  apply unique guarded (cursor + 7 + withdrawalPos j) gBound
  · have := withdrawalPos_bound j jBound
    omega
  · exact NIO_Cpi.forest_index_separation cursor guarded (withdrawalPos j) guardMode cursorBound
#print axioms forest_key_exclusion

theorem pair_key_exclusion (key : Nat → Nat) (len cursor guarded j : Nat)
    (unique : UniqueKeys key len) (gBound : guarded < len)
    (tokenBound : cursor + 5 + 5 ≤ len) (jBound : j < 5)
    (guardMode : guarded ≤ cursor) :
    key guarded ≠ key (cursor + 5 + withdrawalPos j) := by
  apply unique guarded (cursor + 5 + withdrawalPos j) gBound
  · have := withdrawalPos_bound j jBound
    omega
  · exact NIO_Cpi.pair_index_separation cursor guarded (withdrawalPos j) guardMode
#print axioms pair_key_exclusion

/-- A source-key certificate becomes physical separation only with interpretation. -/
theorem physical_exclusion (key cell : Nat → Nat)
    (compatible : NIO_Cpi.CellKeyCompatible key cell) (guarded passed : Nat)
    (nativeKeyExclusion : key guarded ≠ key passed) : cell guarded ≠ cell passed :=
  NIO_Cpi.distinct_key_cells key cell compatible guarded passed nativeKeyExclusion
#print axioms physical_exclusion
end NIO_Infos
