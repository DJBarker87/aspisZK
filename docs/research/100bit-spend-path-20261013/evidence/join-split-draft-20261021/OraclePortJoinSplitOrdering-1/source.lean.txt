import OraclePortJoinSplitCore

/-! The frozen caller's ?-propagation cannot be replaced by dV's eager Bool
conjunction using child verdict equality alone. This is an interface-level
counterexample and a conditional theorem about the actual verifySlots body;
no concrete malformed frozen proof or complete source execution is assumed. -/
set_option autoImplicit false
namespace AspisR1.OraclePortJoinSplitOrdering
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open OraclePortCompactDraft OraclePortSelectedDraft OraclePortBatchDraft

def eager (first rest : Program Bytes State Bool) : Program Bytes State Bool :=
  bind first fun ok => bind rest fun tail => .done (ok && tail)

def shortCircuit (first rest : Program Bytes State Bool) : Program Bytes State Bool :=
  bind first fun ok => if ok then rest else .done false

theorem rejected_read_counterexample (address : Bytes) (H : Bytes → State) :
    eager (.done false) (.ask address fun _ => .done true) ≠
      shortCircuit (.done false) (.ask address fun _ => .done true) := by
  intro same
  have lengths := congrArg (fun program => (eval H program).1.length) same
  simp only [eager,shortCircuit,eval_bind,eval,List.length_append,
    List.length_cons,List.length_nil,Bool.false_eq_true,if_false] at lengths
  omega

/-- An actual dV batch with a rejecting first slot and a reading suffix
cannot equal a source-shaped short-circuit batch with identical children.
Existence/reachability of p/q/H with these hypotheses is not asserted here. -/
theorem verifySlots_rejecting_suffix
    (p : Parsed) (q : Fin 22 → Fin 262144) (head : Nat × Nat)
    (tail : List (Nat × Nat)) (H : Bytes → State)
    (rejects : (eval H (verifySlot p q head.1 head.2)).2 = false)
    (reads : 0 < (eval H (verifySlots p q tail)).1.length) :
    verifySlots p q (head::tail) ≠
      shortCircuit (verifySlot p q head.1 head.2) (verifySlots p q tail) := by
  intro same
  have lengths := congrArg (fun program => (eval H program).1.length) same
  simp only [verifySlots,shortCircuit,eval_bind,eval,rejects,
    Bool.false_eq_true,if_false,List.length_append,List.length_nil] at lengths
  omega

#print axioms rejected_read_counterexample
#print axioms verifySlots_rejecting_suffix
end AspisR1.OraclePortJoinSplitOrdering
