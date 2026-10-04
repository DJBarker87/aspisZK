import AspisV8R19.IndependentMeanFixedTape
import AspisV8R19.OracleProgramOps
import AspisV8R19.R584IndependentBlockSampler
import AspisV8R19.R580SourceWordStream

set_option autoImplicit false
namespace AspisV8R19.R589IndexedReplyExecution
open MemoizedProgramLaw OracleProgramOps IndependentMeanFixedTape
variable {I A O R : Type}

def runIndexed (answer : Nat → A) : Program I A O → Nat → View I A O × Nat
  | .done o, cursor => (([],o),cursor)
  | .ask i next, cursor =>
      let tail := runIndexed answer (next (answer cursor)) (cursor+1)
      (((i,answer cursor)::tail.1.1,tail.1.2),tail.2)

theorem runIndexed_bind (answer : Nat → A) (program : Program I A O)
    (next : O → Program I A R) (cursor : Nat) :
    runIndexed answer (bind program next) cursor =
      let first := runIndexed answer program cursor
      let second := runIndexed answer (next first.1.2) first.2
      ((first.1.1++second.1.1,second.1.2),second.2) := by
  induction program generalizing cursor with
  | done o => rfl
  | ask i k ih => simp only [OracleProgramOps.bind,runIndexed,ih,List.cons_append]

theorem evalTape_runIndexed (program : Program I A O) (fuel : Nat)
    (within : Within program fuel) (tape : Fin fuel → A) (answer : Nat → A)
    (cursor : Nat) (agree : ∀ i : Fin fuel, tape i=answer (cursor+i.val)) :
    evalTape within tape = (runIndexed answer program cursor).1 := by
  induction within generalizing cursor with
  | done o n => rfl
  | ask i next n branches ih =>
      have hfirst : tape 0=answer cursor := by simpa only [Fin.val_zero,Nat.add_zero] using agree 0
      have htail : ∀ j : Fin n, tape j.succ=answer ((cursor+1)+j.val) := by
        intro j
        simpa only [Fin.val_succ,Nat.add_assoc,Nat.add_comm 1 j.val] using agree j.succ
      have hrec := ih (tape 0) (fun j => tape j.succ) (cursor+1) htail
      simp only [evalTape,headTailEquiv,Equiv.coe_fn_mk,runIndexed]
      rw [hrec,hfirst]

open R584IndependentBlockSampler R580SourceWordStream SourceDuplexStep SamplerWords
open R421UniformMasked31Block R442RejectionAlphabet R445InitialBlockRejectionLaw
open R572SequentialWordMass

def indexedResult (answer : Nat → A) (program : Program I A O) (cursor : Nat) : O × Nat :=
  ((runIndexed answer program cursor).1.2,(runIndexed answer program cursor).2)

theorem indexedResult_bind (answer : Nat → A) (program : Program I A O)
    (next : O → Program I A R) (cursor : Nat) :
    indexedResult answer (bind program next) cursor =
      let first := indexedResult answer program cursor
      indexedResult answer (next first.1) first.2 := by
  simp only [indexedResult,runIndexed_bind]

def blockCursorAt (answer : Nat → State) (n : Nat) : BlockCursor :=
  ⟨answer ((n-1)/8),localIndex n⟩

def nextBlock (n : Nat) : Nat := (n-1)/8+1

def blockWord (answer : Nat → State) (n : Nat) : Nat :=
  word (answer (n/8)) ⟨n%8,by omega⟩

def blockAnswer (answer : Nat → State) (n : Nat) : Option (Fin modulus) :=
  alphabetEquiv modulus ((splitBlock31Equiv (answer (n/8))).2 ⟨n%8,by omega⟩)

theorem block_mask (answer : Nat → State) (n : Nat) :
    ((alphabetEquiv modulus).symm (blockAnswer answer n)).val = masked 31 (blockWord answer n) := by
  unfold blockAnswer
  rw [Equiv.symm_apply_apply]
  exact masked31_value _ _

theorem readBlock_indexed (answer : Nat → State) (n : Nat) :
    indexedResult answer (readBlockProgram (blockCursorAt answer n)) (nextBlock n) =
      ((blockWord answer n,blockCursorAt answer (n+1)),nextBlock (n+1)) := by
  by_cases hn : n=0
  · subst n
    simp only [readBlockProgram,blockCursorAt,localIndex,blockWord,nextBlock,
      indexedResult,runIndexed,Nat.zero_sub,Nat.zero_div,Nat.zero_mod,↓reduceIte]
    rfl
  · have hlocal : (localIndex n).val=(n-1)%8+1 := by simp only [localIndex,hn,↓reduceIte]
    by_cases hr : (n-1)%8=7
    · have hdiv : n/8=(n-1)/8+1 := by omega
      have hmod : n%8=0 := by omega
      have hindex : (localIndex n).val=8 := by omega
      simp only [readBlockProgram,blockCursorAt,hindex,↓reduceDIte,indexedResult,runIndexed,
        blockWord,nextBlock,hdiv,hmod,Nat.add_sub_cancel,localIndex,
        show ¬n+1=0 by omega,↓reduceIte]
    · have hdiv : n/8=(n-1)/8 := by omega
      have hmod : n%8=(n-1)%8+1 := by omega
      have hindex : ¬(localIndex n).val=8 := by omega
      simp only [readBlockProgram,blockCursorAt,hindex,↓reduceDIte,indexedResult,runIndexed,
        blockWord,nextBlock,hdiv,hmod,Nat.add_sub_cancel,localIndex,hn,
        show ¬n+1=0 by omega,↓reduceIte]

theorem limbBlock_indexed (answer : Nat → State) (budget n : Nat) :
    indexedResult answer (limbBlockProgram budget (blockCursorAt answer n)) (nextBlock n) =
      let r := resultEval (blockAnswer answer) (scan budget n)
      ((r.1.map Fin.val,blockCursorAt answer r.2),nextBlock r.2) := by
  induction budget generalizing n with
  | zero => rfl
  | succ budget ih =>
      have hm := block_mask answer n
      cases ha : blockAnswer answer n with
      | none =>
          have hw : masked 31 (blockWord answer n)=modulus := by rw [ha] at hm; exact hm.symm
          simp only [limbBlockProgram,indexedResult_bind,readBlock_indexed,hw,modulus,if_true,
            scan,resultEval,ha]
          exact ih (n+1)
      | some a =>
          have hw : masked 31 (blockWord answer n)=a.val := by rw [ha] at hm; exact hm.symm
          have hne : a.val≠2147483647 := by
            have := a.isLt
            change a.val<2147483647 at this
            omega
          simp only [limbBlockProgram,indexedResult_bind,readBlock_indexed,hw,hne,if_false,
            indexedResult,runIndexed,scan,resultEval,ha,Option.map_some]

#print axioms indexedResult_bind
#print axioms block_mask
#print axioms readBlock_indexed
#print axioms limbBlock_indexed
#print axioms runIndexed_bind
#print axioms evalTape_runIndexed
end AspisV8R19.R589IndexedReplyExecution
