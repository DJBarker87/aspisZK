import R1Z.PV_CB_OwnedEncoder
import R1Z.PV_DL_EncoderRange
open Aeneas Aeneas.Std Result ProverRwFull
namespace R1Z.PV_DL_EncoderFold
set_option autoImplicit false

def step {E : Type} (inst : aspis_core.r0.scalar.CodeField E)
    (q : Array E 1024#usize) (basis : Array E 512#usize) (j : Usize) (p0 p1 : E) : Result (E×E) := do
  let a ← Array.index_usize q (Usize.wrapping_mul 2#usize j)
  let n ← Array.index_usize basis j
  let an ← inst.mul a n
  let p0 ← inst.add p0 an
  let b ← Array.index_usize q (Usize.wrapping_add (Usize.wrapping_mul 2#usize j) 1#usize)
  let bn ← inst.mul b n
  let p1 ← inst.add p1 bn
  ok (p0,p1)

def finite {E : Type} (inst : aspis_core.r0.scalar.CodeField E)
    (q : Array E 1024#usize) (basis : Array E 512#usize) : Nat → Usize → E → E → Result (E×E)
  | 0,_,p0,p1 => ok (p0,p1)
  | fuel+1,j,p0,p1 => do
    let (p0,p1) ← step inst q basis j p0 p1
    finite inst q basis fuel (PV_DL_EncoderRange.advance j) p0 p1

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
    have hj : j.val<512 := by omega
    have advance := PV_DL_EncoderRange.advance_val j hj
    rw [PV_CB_OwnedEncoder.owned.encoder_fold]
    simp only [more,if_true,lift,bind_tc_ok,finite,step,bind_assoc_eq]
    try dsimp only [Aeneas.Std.uncurry]
    try simp only [Aeneas.Std.uncurry,bind_assoc_eq,bind_tc_ok]
    repeat' (apply (Aeneas.Std.bind_eq_iff _ _ _).mpr;intro value hvalue)
    exact ih (PV_DL_EncoderRange.advance j) _ _ (by omega)

#print axioms step
#print axioms finite
#print axioms source
end R1Z.PV_DL_EncoderFold
