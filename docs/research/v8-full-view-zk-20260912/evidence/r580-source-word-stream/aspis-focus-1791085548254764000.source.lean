import AspisV8R19.QM31SamplerProgram
import AspisV8R19.R579FourBlockTape

set_option autoImplicit false
namespace AspisV8R19.R580SourceWordStream
open QM31SamplerProgram SourceDuplexStep SamplerWords
open MemoizedProgramLaw OracleProgramOps R572SequentialWordMass
open R421UniformMasked31Block R442RejectionAlphabet R445InitialBlockRejectionLaw

def advanceSeq (H : DuplexFrames.Bytes → State) (s : State) : Nat → State
  | 0 => s
  | n+1 => (step H (advanceSeq H s n)).2

def blockSeq (H : DuplexFrames.Bytes → State) (s : State) (n : Nat) : State :=
  (step H (advanceSeq H s n)).1

def localIndex (n : Nat) : Fin 9 :=
  if n=0 then 0 else ⟨(n-1)%8+1, by omega⟩

def globalCursor (H : DuplexFrames.Bytes → State) (s : State) (n : Nat) : Cursor :=
  ⟨advanceSeq H s ((n-1)/8+1), blockSeq H s ((n-1)/8), localIndex n⟩

def streamWord (H : DuplexFrames.Bytes → State) (s : State) (n : Nat) : Nat :=
  word (blockSeq H s (n/8)) ⟨n%8,by omega⟩

def streamAnswer (H : DuplexFrames.Bytes → State) (s : State) (n : Nat) :
    Option (Fin modulus) :=
  alphabetEquiv modulus
    ((splitBlock31Equiv (blockSeq H s (n/8))).2 ⟨n%8,by omega⟩)

theorem initial_cursor (H : DuplexFrames.Bytes → State) (s : State) :
    globalCursor H s 0 = ⟨(step H s).2,(step H s).1,0⟩ := by rfl

theorem localIndex_succ (n : Nat) :
    (localIndex (n+1)).val = n%8+1 := by
  simp only [localIndex, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
    ↓reduceIte, Nat.add_sub_cancel]

theorem read_stream (H : DuplexFrames.Bytes → State) (s : State) (n : Nat) :
    (readRun H (globalCursor H s n)).2 =
      (streamWord H s n,globalCursor H s (n+1)) := by
  by_cases hn : n=0
  · subst n
    simp only [readRun, globalCursor, localIndex, streamWord, advanceSeq, blockSeq,
      Nat.zero_sub, Nat.zero_div, Nat.zero_mod, ↓reduceIte]
    rfl
  · have hlocal : (localIndex n).val = (n-1)%8+1 := by simp only [localIndex, hn, ↓reduceIte]
    by_cases hr : (n-1)%8=7
    · have hdiv : n/8=(n-1)/8+1 := by omega
      have hmod : n%8=0 := by omega
      have hindex : (localIndex n).val=8 := by omega
      simp only [readRun, globalCursor, hindex, ↓reduceDIte]
      simp only [streamWord, hdiv, hmod, Nat.add_sub_cancel, blockSeq,
        advanceSeq, localIndex, show ¬n+1=0 by omega, ↓reduceIte]
      rfl
    · have hdiv : n/8=(n-1)/8 := by omega
      have hmod : n%8=(n-1)%8+1 := by omega
      have hindex : ¬(localIndex n).val=8 := by omega
      simp only [readRun, globalCursor, hindex, ↓reduceDIte]
      simp only [streamWord, hdiv, hmod, Nat.add_sub_cancel,
        localIndex, hn, show ¬n+1=0 by omega, ↓reduceIte]

theorem stream_mask (H : DuplexFrames.Bytes → State) (s : State) (n : Nat) :
    ((alphabetEquiv modulus).symm (streamAnswer H s n)).val =
      masked 31 (streamWord H s n) := by
  unfold streamAnswer
  rw [Equiv.symm_apply_apply]
  exact masked31_value _ _

theorem scan_stream (H : DuplexFrames.Bytes → State) (s : State)
    (budget n : Nat) :
    (limbRun H budget (globalCursor H s n)).2 =
      let r := (eval (streamAnswer H s) (scan budget n)).2
      (r.1.map Fin.val,globalCursor H s r.2) := by
  induction budget generalizing n with
  | zero => rfl
  | succ budget ih =>
      have hm := stream_mask H s n
      cases ha : streamAnswer H s n with
      | none =>
          have hw : masked 31 (streamWord H s n) = modulus := by
            rw [ha] at hm
            exact hm.symm
          simp only [limbRun, read_stream, hw, modulus, if_true,
            scan, eval, ha]
          exact ih (n+1)
      | some a =>
          have hw : masked 31 (streamWord H s n) = a.val := by
            rw [ha] at hm
            exact hm.symm
          have hne : a.val ≠ 2147483647 := by
            have := a.isLt
            change a.val < 2147483647 at this
            omega
          simp only [limbRun, read_stream, hw, hne, if_false,
            scan, eval, ha, Option.map_some]

def resultEval {I A O : Type} (answer : I → A) : Program I A O → O
  | .done o => o
  | .ask i next => resultEval answer (next (answer i))

theorem eval_result {I A O : Type} (answer : I → A) (program : Program I A O) :
    (eval answer program).2 = resultEval answer program := by
  induction program with
  | done o => rfl
  | ask i next ih => exact ih (answer i)

theorem resultEval_bind {I A O R : Type} (answer : I → A) (program : Program I A O)
    (next : O → Program I A R) :
    resultEval answer (bind program next) = resultEval answer (next (resultEval answer program)) := by
  induction program with
  | done o => rfl
  | ask i k ih => exact ih (answer i)

theorem resultEval_limbs_succ {p : Nat} (answer : Nat → Option (Fin p))
    (budget count n : Nat) :
    resultEval answer (limbs budget (count+1) n) =
      let first := resultEval answer (scan budget n)
      match first.1 with
      | none => (none,first.2)
      | some a => prependResult a (resultEval answer (limbs budget count first.2)) := by
  rw [limbs, resultEval_bind]
  cases first : resultEval answer (scan budget n) with
  | mk head next =>
      cases head with
      | none => rfl
      | some a => simp only [resultEval_bind, resultEval]

theorem limbs_stream_result (H : DuplexFrames.Bytes → State) (s : State)
    (count n : Nat) :
    (limbsRun H count (globalCursor H s n)).2 =
      let r := resultEval (streamAnswer H s) (limbs 8 count n)
      (r.1.map (List.map Fin.val),globalCursor H s r.2) := by
  induction count generalizing n with
  | zero => rfl
  | succ count ih =>
      have hs := scan_stream H s 8 n
      rw [eval_result] at hs
      rw [resultEval_limbs_succ]
      simp only [limbsRun, hs]
      cases hr : resultEval (streamAnswer H s) (scan 8 n) with
      | mk head next =>
          cases head with
          | none => simp only [Option.map_none]
          | some a =>
              simp only [Option.map_some, ih]
              cases ht : resultEval (streamAnswer H s) (limbs 8 count next) with
              | mk result stop =>
                  cases result with
                  | none => simp only [prependResult, Option.map_none]
                  | some xs => simp only [prependResult, Option.map_some, List.map_cons]

theorem limbs_stream (H : DuplexFrames.Bytes → State) (s : State)
    (count n : Nat) :
    (limbsRun H count (globalCursor H s n)).2 =
      let r := (eval (streamAnswer H s) (limbs 8 count n)).2
      (r.1.map (List.map Fin.val),globalCursor H s r.2) := by
  rw [eval_result]
  exact limbs_stream_result H s count n

theorem challenge_stream (H : DuplexFrames.Bytes → State) (s : State) :
    (challengeRun H s).2 =
      let r := (eval (streamAnswer H s) (limbs 8 4 0)).2
      (r.1.map (List.map Fin.val),(globalCursor H s r.2).state) := by
  change ((limbsRun H 4 ⟨(step H s).2,(step H s).1,0⟩).2.1,
    (limbsRun H 4 ⟨(step H s).2,(step H s).1,0⟩).2.2.state) = _
  rw [← initial_cursor, limbs_stream]

#print axioms eval_result
#print axioms resultEval_bind
#print axioms resultEval_limbs_succ
#print axioms limbs_stream_result
#print axioms limbs_stream
#print axioms challenge_stream
#print axioms scan_stream
#print axioms initial_cursor
#print axioms localIndex_succ
#print axioms read_stream
#print axioms stream_mask
end AspisV8R19.R580SourceWordStream
