import AspisR1S9ActualWeightsNewBoxNewV3.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1S9ComplementTwoStepNormalizationV1
open AspisR1S9ActualWeightsNewBoxNewV3
abbrev Q := field.QM31
abbrev V := Array Q 10#usize

/-- The emitted original complement-loop body, parameterised over its missing
Std array iterator primitive. Arithmetic and array operations remain concrete. -/
def body {I : Type} (next : I → Result (Option Usize × I))
    (iter : I) (absorption : V) : Result (ControlFlow (I × V) V) := do
  let (o, iter1) ← next iter
  match o with
  | none => ok (done absorption)
  | some coordinate =>
    let q ← Array.index_usize absorption coordinate
    let q1 ← field.QM31.sub field.QM31.ONE q
    let a ← Array.update absorption coordinate q1
    ok (cont (iter1, a))

def run {I : Type} (next : I → Result (Option Usize × I))
    (iter : I) (a : V) : Result V :=
  loop (fun s : I × V => body next s.1 s.2) (iter, a)

theorem run_none {I : Type} (next : I → Result (Option Usize × I))
    (i j : I) (a : V) (h : next i = .ok (none,j)) : run next i a = .ok a := by
  unfold run
  rw [loop.eq_def]
  simp [body, h]

theorem run_some {I : Type} (next : I → Result (Option Usize × I))
    (i j : I) (a : V) (n : Usize) (h : next i = .ok (some n,j)) :
    run next i a = (do
      let q ← Array.index_usize a n
      let q1 ← field.QM31.sub field.QM31.ONE q
      let a1 ← Array.update a n q1
      run next j a1) := by
  unfold run
  rw [loop.eq_def]
  simp only [body, h]
  cases hr : Array.index_usize a n <;> simp [hr]
  case ok q =>
    cases hs : field.QM31.sub field.QM31.ONE q <;> simp [hs]
    case ok q1 =>
      cases hu : Array.update a n q1 <;> simp [hu]

/-- Full Result equality: all arithmetic/index failures and divergence are
preserved. The only iterator facts needed are its two items and exhaustion.
These facts are still to be connected to the real Std IntoIter implementation. -/
theorem original_loop_eq_two_ordered_writes {I : Type}
    (next : I → Result (Option Usize × I)) (i0 i1 i2 i3 : I) (a : V)
    (h0 : next i0 = .ok (some 7#usize,i1))
    (h1 : next i1 = .ok (some 6#usize,i2))
    (h2 : next i2 = .ok (none,i3)) :
    run next i0 a = (do
      let q ← Array.index_usize a 7#usize
      let q1 ← field.QM31.sub field.QM31.ONE q
      let a1 ← Array.update a 7#usize q1
      let q2 ← Array.index_usize a1 6#usize
      let q3 ← field.QM31.sub field.QM31.ONE q2
      Array.update a1 6#usize q3) := by
  rw [run_some next i0 i1 a 7#usize h0]
  congr 1
  funext q
  congr 1
  funext q1
  congr 1
  funext a1
  rw [run_some next i1 i2 a1 6#usize h1]
  congr 1
  funext q2
  congr 1
  funext q3
  cases hu : Array.update a1 6#usize q3 <;> simp [hu, run_none next i2 i3 _ h2]

#print axioms original_loop_eq_two_ordered_writes
end AspisR1S9ComplementTwoStepNormalizationV1
