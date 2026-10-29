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
theorem return_result {α : Type} (r : Result α) :
    (do let value ← r; .ok value) = r := by
 cases r <;> rfl

/-- The actual 0..4 caller schedule, including arbitrary fail/div callback results. -/
theorem source_schedule (step : Four14 → Usize → Result Four14) (state : Four14) :
 source step state = (do
   let s1 ← step state 0#usize
   let s2 ← step s1 1#usize
   let s3 ← step s2 2#usize
   step s3 3#usize) := by
 have n0 : next 0#usize = .ok (some 0#usize,1#usize) := rfl
 have n1 : next 1#usize = .ok (some 1#usize,2#usize) := rfl
 have n2 : next 2#usize = .ok (some 2#usize,3#usize) := rfl
 have n3 : next 3#usize = .ok (some 3#usize,4#usize) := rfl
 have n4 : next 4#usize = .ok (none,4#usize) := rfl
 simp only [source,run,n0,n1,n2,n3,n4,bind_tc_ok,return_result]
theorem source_link : PV_B3P_Link_slice14 source := by
 intro step state
 rw [source_schedule]
 simp only [PV_B3P_Binding9227.usize_plan,return_result]
 rfl
#print axioms return_result
#print axioms source_schedule
#print axioms source_link
end PV_B3Q_FourSlice
