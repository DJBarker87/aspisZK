import R1Z.ProverCommitRoundOutput48
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_RoundTerms44
open Aeneas Aeneas.Std
open ProverCommitWideOps48 ProverCommitRoundLoop48 ProverCommitCounterList48

def children (n : Nat) (d s t : Usize) : List Triple :=
  (counters n t).map (fun t => (d,s,t))
def lanes (n : Nat) (d s : Usize) : List Triple :=
  (counters n s).flatMap (fun s => children 4 d s 0#usize)
def fibres (n : Nat) (d : Usize) : List Triple :=
  (counters n d).flatMap (fun d => lanes 4 d 0#usize)

theorem terms_append (q w : Nat → Raw) (us vs : List Triple) (k : Nat) :
    terms q w (us ++ vs) k = terms q w us k + terms q w vs k := by
  induction us with
  | nil => simp only [List.nil_append,terms,zero_add]
  | cons u us ih =>
    simp only [List.cons_append,terms,ih,add_assoc]

theorem children_cons (n : Nat) (d s t : Usize) :
    children (n+1) d s t = (d,s,t) :: children n d s (Usize.wrapping_add t 1#usize) := rfl

theorem lanes_cons (n : Nat) (d s : Usize) :
    lanes (n+1) d s = children 4 d s 0#usize ++ lanes n d (Usize.wrapping_add s 1#usize) := rfl

theorem fibres_cons (n : Nat) (d : Usize) :
    fibres (n+1) d = lanes 4 d 0#usize ++ fibres n (Usize.wrapping_add d 1#usize) := rfl

theorem indices (n : Nat) : fibres n 0#usize = ProverCommitRoundOutput48.indices n := rfl
#print axioms terms_append
#print axioms children_cons
#print axioms lanes_cons
#print axioms fibres_cons
#print axioms indices
end R1Z.PV_RunJoin_RoundTerms44
