import PV_EVH_EntropyReturnFootprint
set_option autoImplicit false
namespace PV_EVH_ReturnRegisterLoads
open PV_EVH_StackZero (State)
open PV_EVH_StackStores (Store Outside)
open PV_EVH_EntropyCallerLayout (mask result caller)
open PV_EVH_EntropyReturnFootprint

/-- One actual 16-byte XMM reload. precedingStores counts the already executed
stores, so this does not move the six interleaved loads to the branch entry. -/
structure Load where
  pc : Nat
  register : Nat
  address : Nat
  precedingStores : Nat
  deriving DecidableEq

def loads (sp : Nat) : List Load :=
  [⟨0x14595d,0,sp,0⟩,⟨0x145962,1,sp+16,0⟩,
   ⟨0x14597a,2,sp+32,2⟩,⟨0x14597f,3,sp+48,2⟩,
   ⟨0x145997,4,mask sp,4⟩,⟨0x14599c,5,mask sp+16,4⟩]

/-- Every earlier or later return store is outside the ORIGINAL register-load
sources. Captured values may therefore be used by the ordered-store law;
this is not an assertion of register clearing or native event silence. -/
theorem source_outside (sp p : Nat) (w : State)
    (hp : (sp ≤ p ∧ p < sp+64) ∨ (mask sp ≤ p ∧ p < mask sp+32))
    (s : Store) (hs : s ∈ stores sp w) : Outside s p := by
  simp only [stores,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [Outside,stageFieldHigh,stageFieldLow,stageSeedLow,stageSeedHigh,
      stageMaskHigh,stageMaskLow,returnSeedHigh,returnMaskHigh,returnMaskLow,
      returnSeedLow,returnFieldHigh,returnFieldLow,tag,result,mask,caller] at *
    omega

/-- The six register values are read from the current memory at their actual
interleaved positions, rather than assuming independent register answers.
All sixteen lanes are symbolic. Source-to-machine association stays V370;
recording these snapshots in the actual L3 family remains MOVE-L3. -/
theorem current_reload (sp : Nat) (w : State) (l : Load) (hl : l ∈ loads sp)
    (i : Nat) (hi : i < 16) :
    (PV_EVH_StackStores.run ((stores sp w).take l.precedingStores) w).memory
      (l.address+i) = w.memory (l.address+i) := by
  apply PV_EVH_StackStores.outside_all
  intro s hs
  apply source_outside sp (l.address+i) w ?_ s (List.mem_of_mem_take hs)
  simp only [loads,List.mem_cons,List.not_mem_nil,or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [mask,caller]
    omega

/-- A register snapshot is private machine-state evidence, not a public event
containing entropy bytes. No additional load answer or per-field seed is used. -/
def captured (sp : Nat) (w : State) (l : Load) : Nat → Nat :=
  fun i => (PV_EVH_StackStores.run ((stores sp w).take l.precedingStores) w).memory (l.address+i)

theorem captured_value (sp : Nat) (w : State) (l : Load) (hl : l ∈ loads sp)
    (i : Nat) (hi : i < 16) : captured sp w l i = w.memory (l.address+i) :=
  current_reload sp w l hl i hi

#print axioms source_outside
#print axioms current_reload
#print axioms captured_value
end PV_EVH_ReturnRegisterLoads
