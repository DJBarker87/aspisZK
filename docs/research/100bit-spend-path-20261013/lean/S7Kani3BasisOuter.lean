import S7Kani2BasisLoop
import S7Kani2PrefixLoop
import ExtractedCurrentM31AddSub
set_option autoImplicit false
namespace S7Kani3BasisOuter
open Aeneas Aeneas.Std Result
open S7Kani2BasisLoop (Basis basis_block_owned)
open S7Kani2PrefixLoop (multiply_word wordMul)
open AspisV8R17.RawReducer

def double (x : U32) : Result U32 :=
  AspisR1Qm31ArithmeticProbe.field.M31.add x x

def t2 (x : U32) : Result U32 := do
  let m ← AspisR1Qm31ArithmeticProbe.field.M31.mul x x
  let m1 ← double m
  AspisR1Qm31ArithmeticProbe.field.M31.sub m1 1#u32

theorem t2_total (x : U32) : ∃ y, t2 x=ok y ∧ y.val<P := by
  obtain ⟨m,hm,_,hmc⟩ := AspisR1.ExtractedCurrentReducer.current_mul_mod x x
  obtain ⟨d,hd,_,hdc⟩ := AspisR1.ExtractedCurrentM31AddSub.current_add_mod m m hmc hmc
  obtain ⟨y,hy,_,hyc⟩ := AspisR1.ExtractedCurrentM31AddSub.current_sub_mod d 1#u32 hdc (by decide)
  exact ⟨y,by simp only [t2,double,hm,hd,hy,bind_tc_ok],hyc⟩

/-- Additive port of the emitted outer level recurrence; double and ONE are
inlined with their concrete source definitions. -/
def basis_levels_owned (basis : Basis) (node : U32) (width n : Usize) : Result Basis := do
  if n ≥ width then ok basis else
    let basis1 ← basis_block_owned AspisR1Qm31ArithmeticProbe.field.M31.mul basis node n 0#usize
    let node1 ← t2 node
    let i ← n*2#usize
    basis_levels_owned basis1 node1 width i
partial_fixpoint

def levels : Nat → Basis → U32 → Usize → Result Basis
 | 0,basis,_,_ => ok basis
 | fuel+1,basis,node,n => do
     let basis1 ← basis_block_owned AspisR1Qm31ArithmeticProbe.field.M31.mul basis node n 0#usize
     let node1 ← t2 node
     let n1 ← n*2#usize
     levels fuel basis1 node1 n1

/-- Full emitted outer schedule equals exactly fuel levels. The actual
production width 64 is fuel=6, n=1; no per-level correspondence is assumed. -/
theorem outer_composition (basis : Basis) (node : U32) (width n : Usize)
    (fuel : Nat) (hw : width.val ≤ 256) (hn : 0<n.val)
    (schedule : n.val*2^fuel=width.val) :
    basis_levels_owned basis node width n=levels fuel basis node n := by
  induction fuel generalizing basis node n with
  | zero =>
      have stop : n ≥ width := by simp only [pow_zero,Nat.mul_one] at schedule; scalar_tac
      rw [basis_levels_owned]
      simp only [stop,if_pos,levels]
  | succ fuel ih =>
      have hp : 0<2^fuel := by positivity
      have hm : n.val ≤ n.val*2^fuel := Nat.le_mul_of_pos_right _ hp
      have hs : n.val*2^fuel*2=width.val := by simpa [pow_succ,Nat.mul_assoc] using schedule
      have running : ¬ n ≥ width := by scalar_tac
      have hdouble : n.val*2 ≤ 256 := by omega
      obtain ⟨n1,hinc,hn1⟩ := AspisR1.ExtractedCurrentReducerOps.tryMk_success
        (ty:=.Usize) (n.val*2) (by scalar_tac)
      have hmul : (n*2#usize : Result Usize)=ok n1 := hinc
      rw [basis_levels_owned]
      simp only [running,if_false,levels,bind_assoc_eq]
      congr 1
      funext basis1
      congr 1
      funext node1
      simp only [hmul,bind_tc_ok]
      exact ih basis1 node1 n1 (by omega) (by rw [hn1]; simpa [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hs)

#print axioms t2_total
#print axioms outer_composition
end S7Kani3BasisOuter
