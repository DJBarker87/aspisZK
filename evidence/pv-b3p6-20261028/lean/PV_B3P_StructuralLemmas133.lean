import PV_B3P_Schedule133
namespace PV_B3P_StructuralLemmas133
open PV_B3P_Schedule133
set_option autoImplicit false

def legacyAuxOption (level : Nat) : Option Nat :=
  if level ≥ 21 then none else some (legacyAux level)
def forestAuxOption (level : Nat) : Option Nat :=
  if level ≥ 24 then none else some (forestAux level)
def forestBlockOption (level : Nat) : Option Nat :=
  if level ≥ 24 then none else some (forestBlock level)

theorem legacy_option (level : Nat) (h : level < 21) :
    legacyAuxOption level = some (legacyAux level) := by
  simp [legacyAuxOption,Nat.not_le.mpr h]
theorem forest_aux_option (level : Nat) (h : level < 24) :
    forestAuxOption level = some (forestAux level) := by
  simp [forestAuxOption,Nat.not_le.mpr h]
theorem forest_block_option (level : Nat) (h : level < 24) :
    forestBlockOption level = some (forestBlock level) := by
  simp [forestBlockOption,Nat.not_le.mpr h]
theorem previous_block_option (level : Nat) (h : level < 24) (hn : level ≠ 0) :
    forestBlockOption (level-1) = some (forestBlock (level-1)) :=
  forest_block_option _ (by omega)

theorem local_table (i : Nat) (hi : i < 4) :
    ([1,5,9,13] : List Nat)[i]? = some (1+4*i) := by
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl <;> rfl

theorem helper_bounds (level : Nat) (h : level < 24) :
    forestAux level < 1008 ∧ forestBlock level < 57 := by
  unfold forestAux forestBlock
  split <;> omega

theorem legacy_aux_bounds (level : Nat) (h : level < 21) : legacyAux level < 960 := by
  unfold legacyAux
  omega

theorem u16_cast_harmless (row : Nat) (h : row < 1024) : row % 65536 = row :=
  Nat.mod_eq_of_lt (by omega)
theorem u8_increment_harmless (count : Nat) (h : count < 2) :
    (count+1) % 256 = count+1 := Nat.mod_eq_of_lt (by omega)

def bump (counts : Nat → Nat) (row : Nat) : Nat → Nat :=
  fun q => if row == q then counts q+1 else counts q

theorem bump_count (history : List Nat) (row : Nat) :
    bump (fun q => history.count q) row = fun q => (row::history).count q := by
  funext q
  by_cases h : row = q
  · subst q
    simp [bump,List.count_cons]
  · simp [bump,List.count_cons,h]

def stateCheck : List Link → (Nat → Nat) → (Nat → Nat) → Except Error Unit
  | [],_,_ => .ok ()
  | item::tail,ps,cs =>
    if item.producer ≥ 1024 || ps item.producer ≥ 2 then
      .error (.endpointCapacity item.producer)
    else if item.consumer ≥ 1024 || cs item.consumer ≥ 2 then
      .error (.endpointCapacity item.consumer)
    else stateCheck tail (bump ps item.producer) (bump cs item.consumer)

theorem counts_refinement (links : List Link) (ps cs : List Nat) :
    stateCheck links (fun q => ps.count q) (fun q => cs.count q) =
      checkEndpoints links ps cs := by
  induction links generalizing ps cs with
  | nil => rfl
  | cons head tail ih =>
    simp only [stateCheck,checkEndpoints]
    split
    · rfl
    · split
      · rfl
      · rw [bump_count,bump_count]
        exact ih _ _

#print axioms legacy_option
#print axioms forest_aux_option
#print axioms forest_block_option
#print axioms previous_block_option
#print axioms local_table
#print axioms helper_bounds
#print axioms legacy_aux_bounds
#print axioms u16_cast_harmless
#print axioms u8_increment_harmless
#print axioms bump_count
#print axioms counts_refinement
end PV_B3P_StructuralLemmas133
