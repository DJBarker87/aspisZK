import R1Z.PV_RDCD4_RadixBlock
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RDCD4_RadixLoop
open Aeneas Aeneas.Std Result ControlFlow PV_RDCD4_LazyComponents PV_RDCD4_RadixBlock

def step (poly : Array Q 28#usize) (powers : Array Q 3#usize)
    (prepared : Prepared) (n : Nat) (acc : Q) : Result Q := do
  let acc ← F.pmul prepared acc
  let bv ← block poly powers n
  F.add acc bv

def body (poly : Array Q 28#usize) (powers : Array Q 3#usize)
    (prepared : Prepared) (state : Nat × Q) : Result (ControlFlow (Nat × Q) Q) :=
  if state.1 > 0 then do
    let n := state.1-1
    let acc ← step poly powers prepared n state.2
    ok (cont (n,acc))
  else ok (done state.2)

def source (poly : Array Q 28#usize) (powers : Array Q 3#usize)
    (prepared : Prepared) (n : Nat) (acc : Q) : Result Q :=
  loop (body poly powers prepared) (n,acc)

def finite (poly : Array Q 28#usize) (powers : Array Q 3#usize)
    (prepared : Prepared) : Nat → Q → Result Q
  | 0,acc => ok acc
  | n+1,acc => do
    let acc ← step poly powers prepared n acc
    finite poly powers prepared n acc

theorem binding (poly : Array Q 28#usize) (powers : Array Q 3#usize)
    (prepared : Prepared) (n : Nat) (acc : Q) :
    source poly powers prepared n acc = finite poly powers prepared n acc := by
  induction n generalizing acc with
  | zero =>
    rw [source,loop.eq_def]
    simp [body,finite]
  | succ n ih =>
    rw [source,loop.eq_def]
    simp only [body,Nat.succ_pos,if_true,Nat.add_sub_cancel,finite]
    cases h : step poly powers prepared n acc with
    | ok out =>
      simp only [h,bind_tc_ok]
      exact ih out
    | fail e => simp [h]
    | div => simp [h]
#print axioms binding
end R1Z.PV_RDCD4_RadixLoop
