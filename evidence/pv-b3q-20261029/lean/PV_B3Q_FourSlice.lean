import PV_B3P_ClosureLinks14227
namespace PV_B3Q_FourSlice
open Aeneas Aeneas.Std PV_B3P_Groups14227
set_option autoImplicit false
/-- Same-allocation non-ZST pointers are represented by their slot offsets.
The native pointer add/equality operations stay at V370. -/
def next (index : Usize) : Result (Option Usize × Usize) :=
 if index = 4#usize then .ok (none,index)
 else .ok (some index,Usize.wrapping_add index 1#usize)
/-- A proof measure of five next calls includes the final None; no runtime
iteration bound or callback restriction has been added. -/
def run (step : Four14 → Usize → Result Four14) : Nat → Usize → Four14 → Result Four14
 | 0, _, state => .ok state
 | remaining+1, index, state => do
   let (item, advanced) ← next index
   match item with
   | none => .ok state
   | some slot => do
     let updated ← step state slot
     run step remaining advanced updated
def source (step : Four14 → Usize → Result Four14) (state : Four14) : Result Four14 :=
 run step 5 0#usize state
/-- The actual 0..4 caller schedule, including arbitrary fail/div callback results. -/
theorem source_schedule (step : Four14 → Usize → Result Four14) (state : Four14) :
 source step state = (do
   let s1 ← step state 0#usize
   let s2 ← step s1 1#usize
   let s3 ← step s2 2#usize
   step s3 3#usize) := by
 simp only [source,run,next]
 rfl
theorem source_link : PV_B3P_Link_slice14 source := by
 intro step state
 rw [source_schedule]
 rfl
#print axioms source_schedule
#print axioms source_link
end PV_B3Q_FourSlice
