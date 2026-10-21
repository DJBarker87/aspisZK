import R1Z.BuilderDropFields

/-! Compose arbitrary effects satisfying the projected store contract, rather
than identifying them with the heap model's concrete wipe implementation. -/
set_option autoImplicit false
namespace R1Z.BuilderDropStoreComposition
open BuilderDropObservation BuilderDropFields

def runStores (store : Nat → Memory → Memory) : List Nat → Memory → Memory
  | [], memory => memory
  | base::rest, memory => runStores store rest (store base memory)

theorem stores_frame (store : Nat → Memory → Memory)
    (contract : ∀ base, Frame (wordBytes base) (store base))
    (bases : List Nat) :
    Frame (bases.flatMap wordBytes) (runStores store bases) := by
  induction bases with
  | nil => intro memory j _; rfl
  | cons base rest ih =>
    exact frame_compose (wordBytes base) (rest.flatMap wordBytes)
      (store base) (runStores store rest) (contract base) ih

def runColumn (store : Nat → Memory → Memory) (base words : Nat) : Memory → Memory :=
  runStores store ((List.range words).map (fun i => base+4*i))

theorem column_store_frame (store : Nat → Memory → Memory)
    (contract : ∀ base, Frame (wordBytes base) (store base)) (base words : Nat) :
    Frame (columnBytes base words) (runColumn store base words) := by
  simpa only [runColumn,columnBytes,List.flatMap_map,Function.comp_def] using
    stores_frame store contract ((List.range words).map (fun i => base+4*i))

def runFields (store : Nat → Memory → Memory) : List (Nat × Nat) → Memory → Memory
  | [], memory => memory
  | (base,words)::rest, memory => runFields store rest (runColumn store base words memory)

/-- One word's dynamic-frame certificate suffices for any finite number of
columns and arbitrary lengths; no whole-destructor solver check is needed. -/
theorem destructor_frame (store : Nat → Memory → Memory)
    (contract : ∀ base, Frame (wordBytes base) (store base))
    (fields : List (Nat × Nat)) : Frame (fieldsBytes fields) (runFields store fields) := by
  induction fields with
  | nil => intro memory j _; rfl
  | cons f rest ih =>
    exact frame_compose (columnBytes f.1 f.2) (fieldsBytes rest)
      (runColumn store f.1 f.2) (runFields store rest)
      (column_store_frame store contract f.1 f.2) ih

theorem destructor_observation (store : Nat → Memory → Memory)
    (contract : ∀ base, Frame (wordBytes base) (store base))
    (fields : List (Nat × Nat)) (output : List Nat) (memory : Memory)
    (hd : ∀ j ∈ output, j ∉ fieldsBytes fields) :
    observe output (runFields store fields memory) = observe output memory := by
  unfold observe
  apply List.map_congr_left
  intro j hj
  exact destructor_frame store contract fields memory j (hd j hj)

#print axioms stores_frame
#print axioms column_store_frame
#print axioms destructor_frame
#print axioms destructor_observation
end R1Z.BuilderDropStoreComposition
