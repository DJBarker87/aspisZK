import R1Z.PV_CB_EncoderFoldBounds
import R1Z.PV_CB_ForwardRange
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_EncoderFold
open Aeneas Aeneas.Std Result ProverRwFull ProverRwSuccessArithmeticTotal

def step {E : Type} (inst : aspis_core.r0.scalar.CodeField E)
    (q : Array E 1024#usize) (basis : Array E 512#usize) (j : Usize) (p0 p1 : E) : Result (E × E) := do
  let even ← lift (Usize.wrapping_mul 2#usize j)
  let a ← Array.index_usize q even
  let n ← Array.index_usize basis j
  let an ← inst.mul a n
  let p0 ← inst.add p0 an
  let odd ← lift (Usize.wrapping_add (Usize.wrapping_mul 2#usize j) 1#usize)
  let b ← Array.index_usize q odd
  let bn ← inst.mul b n
  let p1 ← inst.add p1 bn
  .ok (p0,p1)
def finite {E : Type} (inst : aspis_core.r0.scalar.CodeField E)
    (q : Array E 1024#usize) (basis : Array E 512#usize) :
    Nat → Usize → E → E → Result (E × E)
  | 0,_,p0,p1 => .ok (p0,p1)
  | fuel+1,j,p0,p1 => do
    let (a,b) ← step inst q basis j p0 p1
    finite inst q basis fuel (PV_CB_ForwardRange.advance j) a b

theorem source {E : Type} (inst : aspis_core.r0.scalar.CodeField E)
    (q : Array E 1024#usize) (basis : Array E 512#usize)
    (fuel : Nat) (j : Usize) (p0 p1 : E) (rank : j.val+fuel=512) :
    PV_CB_OwnedEncoder.owned.encoder_fold inst q basis j p0 p1 =
      finite inst q basis fuel j p0 p1 := by
  induction fuel generalizing j p0 p1 with
  | zero =>
    have done : ¬j<512#usize := by change ¬j.val<512;omega
    rw [PV_CB_OwnedEncoder.owned.encoder_fold]
    simp only [done,if_false,finite]
  | succ fuel ih =>
    have more : j<512#usize := by change j.val<512;omega
    have advance := PV_CB_ForwardRange.advance_val j 512#usize more
    rw [PV_CB_OwnedEncoder.owned.encoder_fold]
    simp only [more,if_true,lift,bind_tc_ok,finite,step,bind_assoc_eq]
    try dsimp only [Aeneas.Std.uncurry]
    try simp only [Aeneas.Std.uncurry,bind_assoc_eq,bind_tc_ok]
    repeat' (apply (Aeneas.Std.bind_eq_iff _ _ _).mpr; intro value hvalue)
    exact ih (PV_CB_ForwardRange.advance j) _ _ (by omega)

 theorem step_total {E : Type} (inst : aspis_core.r0.scalar.CodeField E)
    (mul_total : ∀ a b,Total (inst.mul a b)) (add_total : ∀ a b,Total (inst.add a b))
    (q : Array E 1024#usize) (basis : Array E 512#usize) (j : Usize) (p0 p1 : E)
    (inside : j.val<512) : Total (step inst q basis j p0 p1) := by
  unfold step
  simp only [lift,bind_tc_ok]
  apply bind_total (ProverRwP6ArrayRead.read q _ (PV_CB_EncoderFoldBounds.even j inside));intro a
  apply bind_total (ProverRwP6ArrayRead.read basis j (PV_CB_EncoderFoldBounds.basis j inside));intro n
  apply bind_total (mul_total a n);intro an
  apply bind_total (add_total p0 an);intro next0
  apply bind_total (ProverRwP6ArrayRead.read q _ (PV_CB_EncoderFoldBounds.odd j inside));intro b
  apply bind_total (mul_total b n);intro bn
  apply bind_total (add_total p1 bn);intro next1
  exact ok_total _
#print axioms source
#print axioms step_total
end R1Z.PV_CB_EncoderFold
