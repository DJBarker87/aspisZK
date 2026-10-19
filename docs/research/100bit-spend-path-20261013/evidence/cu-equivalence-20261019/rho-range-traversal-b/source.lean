import OccupancyRangeTraversal

/-! The original Usize Range iterator executes the exact finite index list,
including callback failures and divergence. No callback totality is assumed. -/
set_option autoImplicit false
namespace AspisR1.CuSavingsRangeTraversal
open Aeneas Aeneas.Std Result ControlFlow
abbrev Range := core.ops.range.Range Usize

def word (n : Nat) : Usize := UScalar.ofNatCore (n % 2^UScalarTy.Usize.numBits)
  (Nat.mod_lt _ (by positivity))

theorem word_val (n : Nat) : (word n).val = n % 2^UScalarTy.Usize.numBits := rfl

theorem word_scalar (n : Usize) : word n.val = n := by
  apply UScalar.eq_of_val_eq
  rw [word_val]
  exact Nat.mod_eq_of_lt (by scalar_tac)

def indices (start fuel : Nat) : List Usize := (List.range' start fuel).map word

def traverse {S : Type} (step : Usize → S → Result S) : List Usize → S → Result S
  | [],state => .ok state
  | index::tail,state => do let next ← step index state;traverse step tail next

def body {S : Type} (step : Usize → S → Result S) (input : Range × S) :
    Result (ControlFlow (Range × S) S) := do
  let (item,next) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize input.1
  match item with
  | none => .ok (.done input.2)
  | some index => do
    let state ← step index input.2
    .ok (.cont (next,state))

theorem loop_eq {S : Type} (step : Usize → S → Result S) (fuel : Nat)
    (range : Range) (state : S) (hspan : range.start.val+fuel = range.«end».val) :
    loop (body step) (range,state) = traverse step (indices range.start.val fuel) state := by
  induction fuel generalizing range state with
  | zero =>
    have hn := OccupancyRangeTraversal.next_done range (by omega)
    rw [loop]
    simp only [body,hn,bind_tc_ok,indices,List.range'_zero,List.map_nil,traverse]
  | succ fuel ih =>
    obtain ⟨next,hn,hstart,hend,_⟩ := OccupancyRangeTraversal.next_step range (by omega)
    have hspan' : next.start.val+fuel=next.«end».val := by rw [hstart,hend];omega
    rw [loop]
    simp only [body,hn,bind_tc_ok,indices,List.range'_succ,List.map_cons,word_scalar,traverse]
    cases hs : step range.start state with
    | fail error => simp only [hs,bind_tc_fail]
    | div => simp only [hs,bind_tc_div]
    | ok output =>
      simp only [hs,bind_tc_ok]
      simpa only [hstart,indices] using ih next output hspan'

#print axioms word_scalar
#print axioms loop_eq
end AspisR1.CuSavingsRangeTraversal
