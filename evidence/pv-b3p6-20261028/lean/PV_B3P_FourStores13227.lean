import PV_B3P_SliceStore13227
namespace PV_B3P_Binding13227
open Aeneas Aeneas.Std PV_B3P_Binding9227 Result
set_option autoImplicit false

def store_four13 {α : Type} (compute : Usize → Result α) (output : Array α 4#usize) := do
  let a ← compute 0#usize
  let output ← Array.update output 0#usize a
  let b ← compute 1#usize
  let output ← Array.update output 1#usize b
  let c ← compute 2#usize
  let output ← Array.update output 2#usize c
  let d ← compute 3#usize
  Array.update output 3#usize d

def four_values13 {α : Type} (compute : Usize → Result α) : Result (Array α 4#usize) := do
  let a ← compute 0#usize
  let b ← compute 1#usize
  let c ← compute 2#usize
  let d ← compute 3#usize
  .ok (Array.make 4#usize [a,b,c,d])

theorem four_store_unroll13 {α : Type} (compute : Usize → Result α) (output : Array α 4#usize) :
    usize_plan (index_store13 compute) 4 0#usize output = store_four13 compute output := rfl

theorem four_store_literal13 {α : Type} (compute : Usize → Result α) (a b c d : α) :
    store_four13 compute (Array.make 4#usize [a,b,c,d]) = four_values13 compute := by
  unfold store_four13 four_values13
  cases h0 : compute 0#usize with
  | fail e => rfl
  | div => rfl
  | ok v0 =>
    cases h1 : compute 1#usize with
    | fail e => rfl
    | div => rfl
    | ok v1 =>
      cases h2 : compute 2#usize with
      | fail e => rfl
      | div => rfl
      | ok v2 =>
        cases h3 : compute 3#usize <;> rfl

theorem slice_four_literal13 {α : Type} (compute : Usize → Result α) (a b c d : α) :
    slice_loop13 (slice_store13 compute) (Array.make 4#usize [a,b,c,d]) = four_values13 compute := by
  rw [iter_mut_restoration13,four_store_unroll13]
  exact four_store_literal13 compute a b c d
#print axioms four_store_unroll13
#print axioms four_store_literal13
#print axioms slice_four_literal13
end PV_B3P_Binding13227
