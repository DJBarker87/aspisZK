import R1Z.ProverCommitGammaCell53
set_option autoImplicit false
namespace R1Z.PV_RunJoin_GammaSourceCell50
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitWideOps48
abbrev Columns := Array (Array Source 1024#usize) 29#usize

def run (c : Columns) (powers : Array Source 29#usize) (row lane : Usize) (acc : Source) : Result Source := do
  let p ← Array.index_usize powers lane
  let a ← Array.index_usize c lane
  let q ← Array.index_usize a row
  let product ← field.wide_exact.WideExact.mul p q
  field.wide_exact.WideExact.add acc product

def phase (c : Columns) (powers : Array Source 29#usize) (row : Usize) : Nat → Usize → Source → Result Source
  | 0,_,acc => ok acc
  | n+1,lane,acc => do
    let next ← run c powers row lane acc
    phase c powers row n (Usize.wrapping_add lane 1#usize) next

theorem complete (c : Columns) (powers : Array Source 29#usize) (row : Usize)
    (n : Nat) (left : U8) (hl : left.val=n) (lane : Usize) (bound : lane.val+n≤29) (acc : Source) :
    gamma53.cell c powers row lane left acc=phase c powers row n lane acc := by
  induction n generalizing left lane acc with
  | zero =>
    have hz : left=0#u8 := by scalar_tac
    rw [gamma53.cell,hz]
    rfl
  | succ n ih =>
    have hn : left≠0#u8 := by scalar_tac
    have dec : (U8.wrapping_sub left 1#u8).val=n := by
      rw [ProverCommitBasisCounter47.sub_one left (by omega)];omega
    have inc : (Usize.wrapping_add lane 1#usize).val=lane.val+1 :=
      ProverCommitPairCounter47.next_val lane (by omega)
    have nextBound : (Usize.wrapping_add lane 1#usize).val+n≤29 := by rw [inc];omega
    rw [gamma53.cell]
    simp only [hn,if_false,lift,bind_tc_ok]
    have tail : ∀ v,gamma53.cell c powers row (Usize.wrapping_add lane 1#usize)
        (U8.wrapping_sub left 1#u8) v=phase c powers row n (Usize.wrapping_add lane 1#usize) v :=
      fun v => ih _ dec _ nextBound v
    simp only [tail,phase,run,bind_assoc]
#print axioms run
#print axioms phase
#print axioms complete
end R1Z.PV_RunJoin_GammaSourceCell50
