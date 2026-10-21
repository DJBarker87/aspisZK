import R1Z.BuilderDropObservation

/-! Compose the projected volatile-store frame contract at byte granularity.
The Vec buffers, rather than their headers alone, are the owned footprint.
No bound on a column length or on its initial contents is used. -/
set_option autoImplicit false
namespace R1Z.BuilderDropFields
open BuilderDropObservation

def wordBytes (base : Nat) : List Nat := (List.range 4).map (base + ·)
def columnBytes (base words : Nat) : List Nat :=
  (List.range words).flatMap (fun i => wordBytes (base + 4*i))
def fieldsBytes (fields : List (Nat × Nat)) : List Nat :=
  fields.flatMap (fun f => columnBytes f.1 f.2)

theorem word_bytes (base j : Nat) : j ∈ wordBytes base ↔ base ≤ j ∧ j < base+4 := by
  simp only [wordBytes, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i,hi,rfl⟩; omega
  · rintro ⟨hl,hh⟩; exact ⟨j-base, by omega, by omega⟩

theorem column_bytes (base words j : Nat) :
    j ∈ columnBytes base words ↔ base ≤ j ∧ j < base+4*words := by
  simp only [columnBytes,List.mem_flatMap,List.mem_range,word_bytes]
  constructor
  · rintro ⟨i,hi,hl,hh⟩; omega
  · rintro ⟨hl,hh⟩
    refine ⟨(j-base)/4,?_,?_,?_⟩ <;> omega

/-- A projected word store cannot reach another field's bytes. -/
theorem word_frame (base : Nat) (memory : Memory) (j : Nat)
    (hj : j < base ∨ base+4 ≤ j) :
    wipe (wordBytes base) memory j = memory j := by
  apply wipe_frame
  rw [word_bytes]; omega

theorem wipe_append (xs ys : List Nat) (memory : Memory) :
    wipe (xs++ys) memory = wipe ys (wipe xs memory) := by
  induction xs generalizing memory with
  | nil => rfl
  | cons a xs ih => exact ih _

/-- Generic composition accepts the exact dynamic write-set property of
individual stores; it does not assume their final values or erase writes. -/
def Frame (owned : List Nat) (effect : Memory → Memory) : Prop :=
  ∀ memory j, j ∉ owned → effect memory j = memory j

theorem frame_compose (xs ys : List Nat) (f g : Memory → Memory)
    (hf : Frame xs f) (hg : Frame ys g) : Frame (xs++ys) (g ∘ f) := by
  intro memory j hj
  have hx : j ∉ xs := by intro h; exact hj (List.mem_append_left _ h)
  have hy : j ∉ ys := by intro h; exact hj (List.mem_append_right _ h)
  exact (hg _ _ hy).trans (hf _ _ hx)

def dropFields : List (Nat × Nat) → Memory → Memory
  | [], memory => memory
  | (base,words)::rest, memory =>
    dropFields rest (wipe (columnBytes base words) memory)

theorem fields_wipe (fields : List (Nat × Nat)) (memory : Memory) :
    dropFields fields memory = wipe (fieldsBytes fields) memory := by
  induction fields generalizing memory with
  | nil => rfl
  | cons f rest ih =>
    simp only [dropFields,fieldsBytes,List.flatMap_cons]
    rw [ih, wipe_append]
    rfl

theorem column_frame (base words : Nat) :
    Frame (columnBytes base words) (wipe (columnBytes base words)) :=
  wipe_frame _

/-- All sixteen columns are instances of this arbitrary-field-list theorem.
This is composition, with no whole-frame solver call and no length bound. -/
theorem fields_frame (fields : List (Nat × Nat)) :
    Frame (fieldsBytes fields) (dropFields fields) := by
  intro memory j hj
  rw [fields_wipe]
  exact wipe_frame _ _ _ hj

theorem fields_observation (fields : List (Nat × Nat)) (output : List Nat)
    (memory : Memory) (hd : ∀ j ∈ output, j ∉ fieldsBytes fields) :
    observe output (dropFields fields memory) = observe output memory := by
  rw [fields_wipe]
  exact wipe_observation _ _ _ hd

#print axioms word_bytes
#print axioms column_bytes
#print axioms word_frame
#print axioms wipe_append
#print axioms frame_compose
#print axioms fields_wipe
#print axioms column_frame
#print axioms fields_frame
#print axioms fields_observation
end R1Z.BuilderDropFields
