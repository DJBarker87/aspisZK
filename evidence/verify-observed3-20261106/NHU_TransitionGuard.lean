import NHU_TransitionStep
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.NHU_TransitionGuard
open NHU_TransitionCut NHU_TransitionStep

def andThen (front tail : Result RR) : Result RR := do
 let status←front
 match status with
 | .Err e=>ok (.Err e)
 | .Ok _=>tail

def guard (p : Public) (level carry : Usize) : Result RR :=
 check p level carry (ok (.Ok ()))

theorem association (p : Public) (level carry : Usize) (next : Result RR) :
 check p level carry next=andThen (guard p level carry) next := by
 unfold guard check andThen
 by_cases skip : level=carry ∧ carry<20#usize
 · simp only [if_pos skip,bind_tc_ok]
 · simp only [if_neg skip,bind_assoc_eq]
   congr 1
   funext want
   congr 1
   funext got
   congr 1
   funext bad
   cases bad <;> rfl

theorem rejected (e : FIq_Native.pool_v1.pair_forest_semantic_terminal.PoolV1PairForestSemanticTerminalErrorV1)
 (tail : Result RR) : andThen (ok (.Err e)) tail=ok (.Err e) := rfl

theorem failed (e : Error) (tail : Result RR) : andThen (fail e) tail=fail e := rfl

theorem diverged (tail : Result RR) : andThen div tail=div := rfl
#print axioms association
#print axioms rejected
#print axioms failed
#print axioms diverged
end AspisR1.NHU_TransitionGuard
end
