import R1Z.PV_RunJoin_BoundaryWords73
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_BoundaryFold73
open Aeneas Aeneas.Std ProverRwFull
open ProverRwP6BoundaryStep (Acc advance)
abbrev Q := aspis_core.field.QM31

def initial (q : Q) : Acc :=
  ⟨U64.wrapping_mul 2#u64 (UScalar.cast .U64 q.c0.a),
   U64.wrapping_mul 2#u64 (UScalar.cast .U64 q.c0.b),
   U64.wrapping_mul 2#u64 (UScalar.cast .U64 q.c1.a),
   U64.wrapping_mul 2#u64 (UScalar.cast .U64 q.c1.b)⟩

def fold (p : Nat → Q) : Nat → Nat → Acc → Acc
  | 0,_,s => s
  | n+1,i,s => fold p n (i+1) (advance (p i) s)

theorem double (w : U32) :
    (U64.wrapping_mul 2#u64 (UScalar.cast .U64 w)).val=2*w.val := by
  have cast : (UScalar.cast .U64 w).val=w.val := by
    rw [UScalar.cast_val_eq]
    change w.val%2^64=w.val
    have h := w.bv.isLt
    change w.val<2^32 at h
    exact Nat.mod_eq_of_lt (by omega)
  rw [U64.wrapping_mul_val_eq,cast]
  simp only [UScalar.ofNatCore_val_eq,UScalar.size_def]
  change (2*w.val)%2^64=2*w.val
  have h := w.bv.isLt
  change w.val<2^32 at h
  exact Nat.mod_eq_of_lt (by omega)

theorem initial_values (q : Q) :
    (initial q).a.val=2*q.c0.a.val ∧ (initial q).b.val=2*q.c0.b.val ∧
    (initial q).c.val=2*q.c1.a.val ∧ (initial q).d.val=2*q.c1.b.val :=
  ⟨double _,double _,double _,double _⟩

theorem initial_bound (q : Q) : PV_RunJoin_BoundaryWords73.bounded 2 (initial q) := by
  obtain ⟨a,b,c,d⟩ := initial_values q
  have ha := q.c0.a.bv.isLt
  have hb := q.c0.b.bv.isLt
  have hc := q.c1.a.bv.isLt
  have hd := q.c1.b.bv.isLt
  change q.c0.a.val<2^32 at ha
  change q.c0.b.val<2^32 at hb
  change q.c1.a.val<2^32 at hc
  change q.c1.b.val<2^32 at hd
  unfold PV_RunJoin_BoundaryWords73.bounded
  rw [a,b,c,d]
  omega

theorem values (p : Nat → Q) (n i used : Nat) (s : Acc)
    (bound : used+n ≤ 29) (safe : PV_RunJoin_BoundaryWords73.bounded used s) :
    let final := fold p n i s
    final.a.val=s.a.val+PV_RunJoin_BoundaryWords73.sum (fun k => (p k).c0.a) n i ∧
    final.b.val=s.b.val+PV_RunJoin_BoundaryWords73.sum (fun k => (p k).c0.b) n i ∧
    final.c.val=s.c.val+PV_RunJoin_BoundaryWords73.sum (fun k => (p k).c1.a) n i ∧
    final.d.val=s.d.val+PV_RunJoin_BoundaryWords73.sum (fun k => (p k).c1.b) n i := by
  induction n generalizing used i s with
  | zero => simp only [fold,PV_RunJoin_BoundaryWords73.sum,Nat.add_zero,and_self]
  | succ n ih =>
    have step := PV_RunJoin_BoundaryWords73.step_values (p i) s used (by omega) safe
    have next := PV_RunJoin_BoundaryWords73.step_bound (p i) s used (by omega) safe
    have tail := ih (i+1) (used+1) (advance (p i) s) (by omega) next
    dsimp only [fold]
    rcases step with ⟨a,b,c,d⟩
    rcases tail with ⟨ta,tb,tc,td⟩
    rw [ta,tb,tc,td,a,b,c,d]
    simp only [PV_RunJoin_BoundaryWords73.sum,Nat.add_assoc,and_self]

#print axioms initial
#print axioms fold
#print axioms double
#print axioms initial_values
#print axioms initial_bound
#print axioms values
end R1Z.PV_RunJoin_BoundaryFold73
