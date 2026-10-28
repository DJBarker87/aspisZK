import R1Z.ProverRwP6CompressSource
import R1Z.ProverRw19LoopBind
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwP6CompressControl
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
variable [ExternalTypes] [ExternalFuns]
abbrev Q := aspis_core.field.QM31
abbrev M := aspis_core.field.M31
abbrev Src := ProverRwP6CompressSource.compress_loop

def dispatch (recur : Q → Q → Usize → Result Q) (values : Slice M)
    (lambda out power : Q) (i : Usize) : Result Q := do
  if i < Slice.len values then
    let m ← Slice.index_usize values i
    let q ← aspis_core.field.QM31.mul_m31 power m
    let out1 ← aspis_core.field.QM31.add out q
    let power1 ← aspis_core.field.QM31.mul power lambda
    recur out1 power1 (Usize.wrapping_add i 1#usize)
  else ok out

theorem source_unfold (values : Slice M) (lambda out power : Q) (i : Usize) :
    Src values lambda out power i = dispatch (Src values lambda) values lambda out power i := by
  unfold Src ProverRwP6CompressSource.compress_loop
  rw [ProverRw19LoopBind.loop_bind]
  unfold ProverRwP6CompressSource.compress_loop.body dispatch
  dsimp only
  by_cases h : i < Slice.len values
  · simp only [h, if_true, bind_assoc_eq, lift, bind_tc_ok]
  · simp only [h, if_false, bind_tc_ok]

theorem dispatch_congr (values : Slice M) (lambda out power : Q) (i : Usize)
    (left right : Q → Q → Usize → Result Q)
    (same : ∀ a b, left a b (Usize.wrapping_add i 1#usize) =
      right a b (Usize.wrapping_add i 1#usize)) :
    dispatch left values lambda out power i = dispatch right values lambda out power i := by
  unfold dispatch
  split
  · repeat' first | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr; intro _ _
    apply same
  · rfl

def finite (values : Slice M) (lambda : Q) : Nat → Q → Q → Usize → Result Q
  | 0, out, power, i => dispatch (fun _ _ _ => .div) values lambda out power i
  | fuel+1, out, power, i => dispatch (finite values lambda fuel) values lambda out power i

theorem loop_finite (values : Slice M) (lambda : Q) (fuel : Nat)
    (out power : Q) (i : Usize) (bound : i.val+fuel=(Slice.len values).val) :
    Src values lambda out power i = finite values lambda fuel out power i := by
  induction fuel generalizing out power i with
  | zero =>
    have cap : ¬ i < Slice.len values := by
      change ¬ i.val < (Slice.len values).val
      omega
    rw [source_unfold]
    simp only [finite,dispatch,cap,if_false]
  | succ fuel ih =>
    rw [source_unfold]
    change dispatch _ _ _ _ _ _ = dispatch _ _ _ _ _ _
    apply dispatch_congr
    intro a b
    apply ih
    have add : (Usize.wrapping_add i 1#usize).val = i.val+1 := by
      rw [Usize.wrapping_add_val_eq]
      change (i.val+1)%UScalar.size .Usize=i.val+1
      rw [Nat.mod_eq_of_lt]
      have big := (Slice.len values).hSize
      omega
    omega

theorem compress_finite (tag : M) (values : Slice M) (lambda : Q) :
    ProverRwP6CompressSource.compress tag values lambda = (do
      let c ← aspis_core.field.CM31.from_m31 tag
      let out ← aspis_core.field.QM31.from_cm31 c
      finite values lambda (Slice.len values).val out lambda 0#usize) := by
  unfold ProverRwP6CompressSource.compress
  repeat' first | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr; intro _ _
  apply loop_finite
  change 0 + _ = _
  omega
#print axioms source_unfold
#print axioms dispatch_congr
#print axioms loop_finite
#print axioms compress_finite
end R1Z.ProverRwP6CompressControl
