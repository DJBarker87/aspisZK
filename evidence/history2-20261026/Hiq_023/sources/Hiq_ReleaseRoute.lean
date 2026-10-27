import Hiq_KeyLaw
set_option autoImplicit false
namespace AspisR1.Hiq_ReleaseRoute
open Aeneas Aeneas.Std

/-- Literal source decision tree: pool_route.rs admitted followed by
r1_pool_adapter.rs process. This is a source model; extraction to the native
entrypoint remains the existing P6/source boundary. -/
inductive Route where
  | first | second | reject
  deriving DecidableEq

def stage1 (data : Slice U8) : Prop := data.val = [3#u8,10#u8] ∨ data.val = [3#u8,11#u8]
def asq8 (data : Slice U8) : Prop := data.val.take 4 = [65#u8,83#u8,81#u8,56#u8]
noncomputable def route (data : Slice U8) : Route := by
  classical
  exact if stage1 data then .first else if asq8 data then .second else .reject

theorem first_iff (data : Slice U8) : route data = .first ↔ stage1 data := by
  classical
  by_cases a : stage1 data <;> by_cases b : asq8 data <;> simp [route,a,b]

theorem second_iff (data : Slice U8) : route data = .second ↔ ¬ stage1 data ∧ asq8 data := by
  classical
  by_cases a : stage1 data <;> by_cases b : asq8 data <;> simp [route,a,b]

theorem reject_iff (data : Slice U8) : route data = .reject ↔ ¬ stage1 data ∧ ¬ asq8 data := by
  classical
  by_cases a : stage1 data <;> by_cases b : asq8 data <;> simp [route,a,b]

#print axioms first_iff
#print axioms second_iff
#print axioms reject_iff
end AspisR1.Hiq_ReleaseRoute
