import R1Z.ProverCommitPairCounter47
/-! P6 denotation of the native chunks_exact(2).zip(basis) evaluator.
The Rust iteration binding is checked separately with a universal callee trace.
This module composes those steps, keeping index/arithmetic errors explicit. -/
set_option autoImplicit false
namespace R1Z.ProverCommitNativePair48
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
abbrev E := field.wide_exact.WideExact

def step (q : Array E 1024#usize) (basis : Array E 512#usize)
    (i : Usize) (p : E × E) : Result (E × E) := do
  let n ← Array.index_usize basis i
  let a ← Array.index_usize q (Usize.wrapping_mul 2#usize i)
  let a ← field.wide_exact.WideExact.mul a n
  let p0 ← field.wide_exact.WideExact.add p.1 a
  let b ← Array.index_usize q (Usize.wrapping_add (Usize.wrapping_mul 2#usize i) 1#usize)
  let b ← field.wide_exact.WideExact.mul b n
  let p1 ← field.wide_exact.WideExact.add p.2 b
  ok (p0,p1)

def range (q : Array E 1024#usize) (basis : Array E 512#usize) :
    Nat → Usize → (E × E) → Result (E × E)
  | 0,_,p => ok p
  | n+1,i,p => do
    let p ← step q basis i p
    range q basis n (Usize.wrapping_add i 1#usize) p

theorem range_finite (q : Array E 1024#usize) (basis : Array E 512#usize)
    (n : Nat) (i : Usize) (p0 p1 : E) :
    range q basis n i (p0,p1) = ProverCommitPairCounter47.finite n q basis i p0 p1 := by
  induction n generalizing i p0 p1 with
  | zero => rfl
  | succ n ih =>
    simp only [range,step,Aeneas.Std.bind_assoc_eq,bind_tc_ok,
      ProverCommitPairCounter47.finite]
    simp only [ih]

theorem range_owner (q : Array E 1024#usize) (basis : Array E 512#usize)
    (n : Nat) (left : U16) (hleft : left.val=n) (i : Usize) (p0 p1 : E) :
    range q basis n i (p0,p1) = pairs q basis i left p0 p1 := by
  rw [range_finite,ProverCommitPairCounter47.source_finite n left hleft]

def evaluate (q : Array E 1024#usize) (basis : Array E 512#usize) (y : E) : Result E := do
  let p ← range q basis 512 0#usize (field.wide_exact.WideExact.ZERO,field.wide_exact.WideExact.ZERO)
  let product ← field.wide_exact.WideExact.mul y p.2
  field.wide_exact.WideExact.add p.1 product

theorem evaluate_owner (q : Array E 1024#usize) (basis : Array E 512#usize) (y : E) :
    evaluate q basis y = AspisR1ProducerRelease47.evaluate q basis y := by
  unfold evaluate AspisR1ProducerRelease47.evaluate
  rw [range_owner q basis 512 512#u16 rfl]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro p hp
  cases p
  rfl

#print axioms range_finite
#print axioms range_owner
#print axioms evaluate_owner
end R1Z.ProverCommitNativePair48
