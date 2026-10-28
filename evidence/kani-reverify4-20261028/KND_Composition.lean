import KND_Schedule
set_option autoImplicit false
namespace KND_Composition
open KND_Schedule KMX_CopyMeaning KMY_WindowComposition
-- Source loop structure: two roots, four wides, 22 words, 10 semantics,
-- two points times two coordinates, two claims, and 64 weights.
def sourceGroups : List (Nat × Nat) :=
 [(1,8),(1,8),(3,32),(2,32),(4,32),(1,16),(22,4),(10,16),
  (4,16),(2,32),(1,16),(64,16),(1,32)]
def sourceSizes : List Nat := sourceGroups.flatMap (fun p => List.replicate p.1 p.2)
theorem source_structure : sourceSizes = emissions.map Prod.snd := by decide
#print axioms source_structure
abbrev State := Nat → Nat
def model (s : Step) (before value : State) : State := window value before s.len s.size
def execute (step : Step → State → State → State) (value : String → State) :
 List Step → State → State
 | [], before => before
 | s::ss, before => execute step value ss (step s before (value s.operation))
-- This premise represents ALL runtime transitions. Missing Kani gates cannot
-- be supplied by the mathematical window model.
theorem compose (step : Step → State → State → State) (value : String → State)
 (ss : List Step) (before : State)
 (valid : ∀ s ∈ ss, ∀ b v, step s b v = model s b v) :
 execute step value ss before = execute model value ss before := by
 induction ss generalizing before with
 | nil => rfl
 | cons s ss ih =>
   simp only [execute]
   rw [valid s (by simp)]
   exact ih _ (fun t ht => valid t (by simp [ht]))
theorem byte_law (s : Step) (before value : State) (j : Nat)
 (bound : j < s.len + s.size) :
 model s before value j = if j<s.len then before j else value (j-s.len) :=
 KMY_SerializerComposition.append_window value before s.len s.size j bound
-- Pointwise version matches the live-buffer scope of each Kani assertion.
theorem live_transport (s : Step) (before reference value actual : State)
 (kept : ∀ j, j<s.len → before j = reference j)
 (runtime : ∀ j, j<s.len+s.size → actual j = model s before value j)
 (j : Nat) (bound : j<s.len+s.size) : actual j = model s reference value j := by
 rw [runtime j bound, byte_law s before value j bound,
     byte_law s reference value j bound]
 by_cases h : j<s.len
 · simp only [if_pos h]
   exact kept j h
 · simp only [if_neg h]
#print axioms live_transport
theorem schedule_composition (step : Step → State → State → State)
 (value : String → State) (before : State)
 (valid : ∀ s ∈ schedule, ∀ b v, step s b v = model s b v) :
 execute step value schedule before = execute model value schedule before :=
 compose step value schedule before valid
#print axioms compose
#print axioms byte_law
#print axioms schedule_composition
end KND_Composition
