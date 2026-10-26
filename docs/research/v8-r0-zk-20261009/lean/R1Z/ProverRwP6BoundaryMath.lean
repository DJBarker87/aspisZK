import R1Z.ProverRwP6BoundaryNoWrap
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwP6BoundaryMath
open Aeneas Aeneas.Std Result ProverRwFull
abbrev Acc := ProverRwP6BoundaryStep.Acc
abbrev Q := aspis_core.field.QM31
def bounded (n : Nat) (s : Acc) : Prop :=
  s.a.val ≤ n*4294967295 ∧ s.b.val ≤ n*4294967295 ∧
  s.c.val ≤ n*4294967295 ∧ s.d.val ≤ n*4294967295

theorem step_values (x : Q) (s : Acc) (n : Nat) (hn : n ≤ 29) (hs : bounded n s) :
    let t := ProverRwP6BoundaryStep.advance x s
    t.a.val=s.a.val+x.c0.a.val ∧ t.b.val=s.b.val+x.c0.b.val ∧
    t.c.val=s.c.val+x.c1.a.val ∧ t.d.val=s.d.val+x.c1.b.val := by
  have limit := Nat.mul_le_mul_right 4294967295 hn
  rcases hs with ⟨ha,hb,hc,hd⟩
  exact ⟨ProverRwP6BoundaryNoWrap.add_word s.a x.c0.a (ha.trans limit),
    ProverRwP6BoundaryNoWrap.add_word s.b x.c0.b (hb.trans limit),
    ProverRwP6BoundaryNoWrap.add_word s.c x.c1.a (hc.trans limit),
    ProverRwP6BoundaryNoWrap.add_word s.d x.c1.b (hd.trans limit)⟩

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
#print axioms step_values
#print axioms step_bound
end R1Z.ProverRwP6BoundaryMath
