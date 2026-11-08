import PV_STX2_Source7EntryOwnedWellFormed
set_option autoImplicit false
noncomputable section
namespace PV_STX2_Source7ColumnRegistrationFixture
open Aeneas Aeneas.Std PV_EVHB_OWNER PV_EVHB_RawVecOwner
open PV_STX2_Source7EntryOwned
/-! Conditional on owner acceptance of the translator patch. A model fixture
for checking whether the first-column registration clause entails registration
of every column. This is not a counterexample to the frozen Rust. -/
def zero : PV_OWN2_Codec.M31 := 0#u32
def column (i : Nat) : alloc.vec.Vec PV_OWN2_Codec.M31 :=
  ⟨if i = 1 then [zero] else [], by split <;> simp <;> scalar_tac⟩
def foundation : Foundation :=
  ⟨⟨List.ofFn (fun i : Fin 16 => column i.val), by simp⟩⟩
def shape : R1Z.PV_FXM_ReserveWorld.Shape := ⟨4, ._Align1Shl2⟩
def empty : Header := ⟨4,0,0,shape,true⟩
def single : Header := ⟨8,1,1,shape,false⟩
def source0 : Place := ⟨0,[4]⟩
def source1 : Place := ⟨1,[0]⟩
def state (seed : OWNER) : OWNER :=
  {world := {seed.world with
    allocator := {seed.world.allocator with metadata := (fun p => if p = 8 then .some (PV_EVHB_RawVecOwner.layout single 1) else .none)}
    frame := {seed.world.frame with slots := (fun id => if id = 0 then .some empty else if id = 1 then .some single else .none)}
    live := fun p => decide (p = 8)
    memory := fun _ => some 0}
   next := 2
   places := fun p => if p = source0 then some 0 else if p = source1 then some 1 else none}
theorem values_at (i : Fin foundation.c1.val.length) :
    values foundation i = if i.val = 1 then [zero] else [] := by
  change (List.ofFn (fun j : Fin 16 => column j.val))[i.val].val = _
  rw [List.getElem_ofFn]
  rfl
theorem wellFormed (seed : OWNER) :
    PV_STX2_OwnerWellFormed.OwnerWellFormed (state seed) := by
  intro p id selected
  simp only [state] at selected
  split at selected
  · cases selected; change 0 < 2; decide
  · split at selected
    · cases selected; change 1 < 2; decide
    · cases selected
theorem receiver0 (seed : OWNER) : receiver (state seed) source0 = some (0,empty) := by
  simp [receiver,PV_EVHB_OwnerMachine.receiver,state,lookup,source0,source1]
theorem receiver1 (seed : OWNER) : receiver (state seed) source1 = some (1,single) := by
  simp [receiver,PV_EVHB_OwnerMachine.receiver,state,lookup,source0,source1]
theorem typed0 (seed : OWNER) :
    PV_OWN2_Codec.TypedMemory 4 PV_OWN2_Codec.decodeM31 (state seed) ⟨source0,[]⟩ := by
  constructor
  · exact ⟨0,empty,receiver0 seed,Or.inr ⟨rfl,rfl⟩,rfl,by decide⟩
  · intro id h read
    rw [receiver0 seed] at read
    cases read
    exact ⟨rfl,by intro i bound; simp at bound⟩
theorem typed1 (seed : OWNER) :
    PV_OWN2_Codec.TypedMemory 4 PV_OWN2_Codec.decodeM31 (state seed) ⟨source1,[zero]⟩ := by
  constructor
  · exact ⟨1,single,receiver1 seed,Or.inl ⟨rfl,rfl⟩,rfl,by decide⟩
  · intro id h read
    rw [receiver1 seed] at read
    cases read
    refine ⟨rfl,?_⟩
    intro i bound
    have eq : i = 0 := by simpa using bound
    subst i
    rfl
#print axioms values_at
#print axioms wellFormed
#print axioms receiver0
#print axioms receiver1
#print axioms typed0
#print axioms typed1
end PV_STX2_Source7ColumnRegistrationFixture
