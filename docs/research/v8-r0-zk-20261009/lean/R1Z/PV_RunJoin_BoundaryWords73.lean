import R1Z.ProverRwP6BoundaryStep
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_BoundaryWords73
open Aeneas Aeneas.Std Result ProverRwFull
abbrev Acc := ProverRwP6BoundaryStep.Acc
abbrev Q := aspis_core.field.QM31
theorem add_word (s : U64) (x : U32) (bound : s.val ≤ 29 * (2^32-1)) :
    (U64.wrapping_add s (UScalar.cast .U64 x)).val = s.val + x.val := by
  have cast : (UScalar.cast .U64 x).val = x.val := by scalar_tac
  rw [U64.wrapping_add_val_eq, cast]
  apply Nat.mod_eq_of_lt
  have hx := x.hSize
  simp only [UScalar.size, UScalarTy.numBits] at *
  change s.val + x.val < 18446744073709551616
  change x.val < 4294967296 at hx
  omega

def bounded (n : Nat) (s : Acc) : Prop :=
  s.a.val ≤ n*4294967295 ∧ s.b.val ≤ n*4294967295 ∧
  s.c.val ≤ n*4294967295 ∧ s.d.val ≤ n*4294967295

theorem step_values (x : Q) (s : Acc) (n : Nat) (hn : n ≤ 29) (hs : bounded n s) :
    let t := ProverRwP6BoundaryStep.advance x s
    t.a.val=s.a.val+x.c0.a.val ∧ t.b.val=s.b.val+x.c0.b.val ∧
    t.c.val=s.c.val+x.c1.a.val ∧ t.d.val=s.d.val+x.c1.b.val := by
  have limit := Nat.mul_le_mul_right 4294967295 hn
  rcases hs with ⟨ha,hb,hc,hd⟩
  exact ⟨add_word s.a x.c0.a (ha.trans limit),
    add_word s.b x.c0.b (hb.trans limit),
    add_word s.c x.c1.a (hc.trans limit),
    add_word s.d x.c1.b (hd.trans limit)⟩

theorem step_bound (x : Q) (s : Acc) (n : Nat) (hn : n ≤ 29) (hs : bounded n s) :
    bounded (n+1) (ProverRwP6BoundaryStep.advance x s) := by
  have hv := step_values x s n hn hs
  rcases hv with ⟨va,vb,vc,vd⟩
  rcases hs with ⟨ha,hb,hc,hd⟩
  have xa : x.c0.a.val ≤ 4294967295 := by scalar_tac
  have xb : x.c0.b.val ≤ 4294967295 := by scalar_tac
  have xc : x.c1.a.val ≤ 4294967295 := by scalar_tac
  have xd : x.c1.b.val ≤ 4294967295 := by scalar_tac
  unfold bounded
  rw [va,vb,vc,vd]
  omega

def sum (q : Nat → U32) : Nat → Nat → Nat
  | 0,_ => 0
  | n+1,j => (q j).val+sum q n (j+1)
#print axioms add_word
#print axioms step_values
#print axioms step_bound
#print axioms sum
end R1Z.PV_RunJoin_BoundaryWords73
