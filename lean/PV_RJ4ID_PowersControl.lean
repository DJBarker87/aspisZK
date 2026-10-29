import R1Z.ProverRwP6PowersFinite
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RJ4ID_PowersControl
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
variable [ExternalTypes] [ExternalFuns]
abbrev W := aspis_core.field.wide_exact.WideExact

/-- Structural interpretation of the deployed prover_powers indexed loop.
The mutable-borrow restoration is explicitly retained at each store. -/
def body {N : Usize} (x : W) (out : Array W N) (p : W) (i : Usize) :
    Result (ControlFlow (Array W N × W × Usize) (Array W N)) := do
  if i < N then
    let (_,back) ← Array.index_mut_usize out i
    let i1 := Usize.wrapping_add i 1#usize
    if i1 < N then
      let p1 ← aspis_core.field.wide_exact.WideExact.mul p x
      ok (cont (back p,p1,i1))
    else ok (cont (back p,p,i1))
  else ok (done out)

def run {N : Usize} (x : W) (out : Array W N) (p : W) (i : Usize) : Result (Array W N) :=
  loop (fun (a,b,c) => body x a b c) (out,p,i)

def dispatch {N : Usize} (recur : Array W N → W → Usize → Result (Array W N))
    (x : W) (out : Array W N) (p : W) (i : Usize) : Result (Array W N) := do
  if i < N then
    let (_,back) ← Array.index_mut_usize out i
    let i1 := Usize.wrapping_add i 1#usize
    if i1 < N then
      let p1 ← aspis_core.field.wide_exact.WideExact.mul p x
      recur (back p) p1 i1
    else recur (back p) p i1
  else ok out

theorem source_unfold {N : Usize} (x : W) (out : Array W N) (p : W) (i : Usize) :
    run x out p i = dispatch (run x) x out p i := by
  unfold run
  rw [ProverRwSuccessPowerTotal.loop_bind]
  unfold body dispatch
  dsimp only
  by_cases h : i < N
  · simp only [h,if_true]
    cases hr : Array.index_mut_usize out i with
    | fail e => simp only [hr,bind_tc_fail]
    | div => simp only [hr,bind_tc_div]
    | ok pair =>
      rcases pair with ⟨old,back⟩
      simp only [hr,bind_tc_ok]
      by_cases last : Usize.wrapping_add i 1#usize < N
      · simp only [last,if_true]
        cases hm : aspis_core.field.wide_exact.WideExact.mul p x <;>
          simp only [hm,bind_tc_ok,bind_tc_fail,bind_tc_div] <;> rfl
      · simp only [last,if_false,bind_tc_ok] <;> rfl
  · simp only [h,if_false,bind_tc_ok]

theorem dispatch_congr {N : Usize} (x : W) (out : Array W N) (p : W) (i : Usize)
    (left right : Array W N → W → Usize → Result (Array W N))
    (same : ∀ a b, left a b (Usize.wrapping_add i 1#usize) =
      right a b (Usize.wrapping_add i 1#usize)) :
    dispatch left x out p i = dispatch right x out p i := by
  unfold dispatch
  split
  · apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro pair hp
    rcases pair with ⟨old,back⟩
    dsimp only
    split
    · apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro next hn
      apply same
    · apply same
  · rfl

def finite {N : Usize} (x : W) : Nat → Array W N → W → Usize → Result (Array W N)
  | 0,out,p,i => dispatch (fun _ _ _ => .div) x out p i
  | fuel+1,out,p,i => dispatch (finite x fuel) x out p i

theorem loop_finite {N : Usize} (x : W) (fuel : Nat)
    (out : Array W N) (p : W) (i : Usize) (bound : i.val+fuel=N.val) :
    run x out p i = finite x fuel out p i := by
  induction fuel generalizing out p i with
  | zero =>
    have cap : ¬ i<N := by change ¬i.val<N.val; omega
    rw [source_unfold]
    simp only [finite,dispatch,cap,if_false]
  | succ fuel ih =>
    rw [source_unfold]
    change dispatch _ _ _ _ _ = dispatch _ _ _ _ _
    apply dispatch_congr
    intro a b
    apply ih
    have add : (Usize.wrapping_add i 1#usize).val = i.val+1 := by
      rw [Usize.wrapping_add_val_eq]
      change (i.val+1)%UScalar.size .Usize=i.val+1
      rw [Nat.mod_eq_of_lt]
      have big := N.hSize
      omega
    omega

def powers (N : Usize) (x : W) : Result (Array W N) := do
  let zero ← aspis_core.field.wide_exact.WideExact.ZERO
  let one ← ProverRwP6PowersSource.aspis_core.field.wide_exact.WideExact.ONE
  run x (Array.repeat N zero) one 0#usize

theorem source (N : Usize) (x : W) :
    powers N x = (do
      let zero ← aspis_core.field.wide_exact.WideExact.ZERO
      let one ← ProverRwP6PowersSource.aspis_core.field.wide_exact.WideExact.ONE
      finite x N.val (Array.repeat N zero) one 0#usize) := by
  unfold powers
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro zero hz
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro one ho
  exact loop_finite x N.val _ _ 0#usize (by change 0+_= _; omega)

#print axioms source_unfold
#print axioms dispatch_congr
#print axioms loop_finite
#print axioms source
end R1Z.PV_RJ4ID_PowersControl
