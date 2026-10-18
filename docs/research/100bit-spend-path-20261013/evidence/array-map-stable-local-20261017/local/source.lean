import EmptyRootExecution

/-! Stable callback map over the actual source Array.map implementation.
Callbacks need succeed only on values present in the input array. -/
set_option autoImplicit false
namespace AspisR1.PoseidonArrayMapStable
open Aeneas Aeneas.Std Result
open AspisV8R19.TraversalRuntime

theorem mapState_stable {T U F : Type} (call : F → T → Result (U × F))
    (f : F) (g : T → U) (xs : List T) :
    (∀ x, x ∈ xs → call f x = .ok (g x,f)) →
      mapState call xs f = .ok (xs.map g,f) := by
  induction xs with
  | nil => intro _; rfl
  | cons x xs ih =>
    intro hstable
    have hx := hstable x (by simp)
    have htail : ∀ y, y ∈ xs → call f y = .ok (g y,f) := by
      intro y hy
      exact hstable y (List.mem_cons_of_mem x hy)
    simp only [mapState,hx,bind_tc_ok,List.map_cons,ih htail]

def mapped {T U : Type} {N : Usize} (a : Array T N) (g : T → U) : Array U N :=
  ⟨a.val.map g, by simpa using a.property⟩

theorem source_success {T U F : Type} {N : Usize}
    (inst : core.ops.function.FnMut F T U) (a : Array T N) (f : F) (g : T → U)
    (hstable : ∀ x, x ∈ a.val → inst.call_mut f x = .ok (g x,f)) :
    core.array.Array.map inst a f = .ok (mapped a g) := by
  have hmap := mapState_stable inst.call_mut f g a.val hstable
  have hsource := core.array.Array.map_success inst a f (a.val.map g) f hmap
  simpa only [mapped] using hsource

#print axioms mapState_stable
#print axioms source_success
end AspisR1.PoseidonArrayMapStable
