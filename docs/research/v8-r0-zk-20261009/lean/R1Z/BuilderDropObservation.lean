import R1Z.BuilderRecordsFields

/-! Sequential observation boundary for zeroization. The footprint includes
owned Vec buffers, not just the inline trace header. This module proves the
heap-model rule; Rust/Charon/Kani correspondence remains the named P6 route.
A compiler fence is silent only for this sequential output observation. -/
set_option autoImplicit false
namespace R1Z.BuilderDropObservation
open Aeneas Aeneas.Std Result
abbrev Memory := Nat → U8

def wipe (addresses : List Nat) (memory : Memory) : Memory :=
  match addresses with
  | [] => memory
  | a :: rest => wipe rest (fun j => if j = a then 0#u8 else memory j)

/-- No store outside the owned footprint, for any length or stored bytes. -/
theorem wipe_frame (addresses : List Nat) (memory : Memory) (j : Nat)
    (hj : j ∉ addresses) : wipe addresses memory j = memory j := by
  induction addresses generalizing memory with
  | nil => rfl
  | cons a rest ih =>
    have hja : j ≠ a := by intro h; apply hj; simp [h]
    have hjr : j ∉ rest := by intro h; apply hj; simp [h]
    rw [wipe, ih _ hjr, if_neg hja]

/-- The observation may contain any number of retained output bytes. -/
def observe (addresses : List Nat) (memory : Memory) : List U8 :=
  addresses.map memory

theorem wipe_observation (owned output : List Nat) (memory : Memory)
    (hdisjoint : ∀ j ∈ output, j ∉ owned) :
    observe output (wipe owned memory) = observe output memory := by
  unfold observe
  apply List.map_congr_left
  intro j hj
  exact wipe_frame owned memory j (hdisjoint j hj)

/-- Total sequential specification; panic and divergence are absent. -/
def dropSpec (owned : List Nat) (memory : Memory) : Result (Unit × Memory) :=
  ok ((),wipe owned memory)

theorem drop_returns_unit (owned : List Nat) (memory : Memory) :
    ∃ after, dropSpec owned memory = ok ((),after) := ⟨_,rfl⟩

/-- Erasing the dropped heap from the result is justified by disjointness,
not by replacing volatile writes with no writes on live memory. -/
theorem drop_outputs (owned output : List Nat) (memory : Memory)
    (hdisjoint : ∀ j ∈ output, j ∉ owned) :
    (do let (unit,after) ← dropSpec owned memory
        ok (unit,observe output after)) = ok ((),observe output memory) := by
  simp only [dropSpec,bind_tc_ok,wipe_observation owned output memory hdisjoint]

/-- A source P6 certificate must supply the actual effect and termination,
for the same source heap footprint. No axiom or source certificate is added. -/
structure P6Route (sourceDrop : Memory → Result (Unit × Memory))
    (owned : List Nat) : Prop where
  specification : ∀ memory, sourceDrop memory = dropSpec owned memory

theorem p6_outputs {sourceDrop : Memory → Result (Unit × Memory)}
    {owned : List Nat} (certificate : P6Route sourceDrop owned)
    (output : List Nat) (memory : Memory)
    (hdisjoint : ∀ j ∈ output, j ∉ owned) :
    (do let (unit,after) ← sourceDrop memory
        ok (unit,observe output after)) = ok ((),observe output memory) := by
  rw [certificate.specification]
  exact drop_outputs owned output memory hdisjoint

#print axioms wipe_frame
#print axioms wipe_observation
#print axioms drop_returns_unit
#print axioms drop_outputs
#print axioms p6_outputs
end R1Z.BuilderDropObservation
