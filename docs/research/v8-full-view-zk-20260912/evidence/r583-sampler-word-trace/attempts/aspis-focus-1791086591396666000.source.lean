import AspisV8R19.R582SequentialTapeExecution

set_option autoImplicit false
namespace AspisV8R19.R583SamplerWordTrace
open R580SourceWordStream R582SequentialTapeExecution QM31SamplerProgram SourceDuplexStep
open MemoizedProgramLaw OracleProgramOps R572SequentialWordMass
open R442RejectionAlphabet R445InitialBlockRejectionLaw SamplerWords

def wordCalls (H : DuplexFrames.Bytes → State) (s : State) (n : Nat) :
    List (DuplexFrames.Bytes × State) :=
  if n=0 ∨ n%8≠0 then [] else calls H (advanceSeq H s (n/8))

def wordTrace (H : DuplexFrames.Bytes → State) (s : State)
    (reads : List (Nat × Option (Fin modulus))) : List (DuplexFrames.Bytes × State) :=
  reads.flatMap (fun r => wordCalls H s r.1)

theorem read_stream_calls (H : DuplexFrames.Bytes → State) (s : State) (n : Nat) :
    (readRun H (globalCursor H s n)).1 = wordCalls H s n := by
  by_cases hn : n=0
  · subst n
    simp only [readRun, globalCursor, localIndex, advanceSeq, blockSeq,
      Nat.zero_sub, Nat.zero_div, Nat.zero_mod, wordCalls, true_or, ↓reduceIte]
    rfl
  · have hlocal : (localIndex n).val = (n-1)%8+1 := by simp only [localIndex, hn, ↓reduceIte]
    by_cases hr : (n-1)%8=7
    · have hdiv : n/8=(n-1)/8+1 := by omega
      have hmod : n%8=0 := by omega
      have hindex : (localIndex n).val=8 := by omega
      simp only [readRun, globalCursor, hindex, ↓reduceDIte, wordCalls, hn, hmod,
        ne_eq, not_true_eq_false, or_self, ↓reduceIte, hdiv]
    · have hmod : n%8≠0 := by omega
      have hindex : ¬(localIndex n).val=8 := by omega
      have hd : n=0 ∨ n%8≠0 := Or.inr hmod
      simp only [readRun, globalCursor, hindex, ↓reduceDIte, wordCalls, if_pos hd]

theorem wordTrace_cons (H : DuplexFrames.Bytes → State) (s : State) (n : Nat)
    (a : Option (Fin modulus)) (reads : List (Nat × Option (Fin modulus))) :
    wordTrace H s ((n,a)::reads) = wordCalls H s n ++ wordTrace H s reads := by
  rfl

theorem scan_stream_trace (H : DuplexFrames.Bytes → State) (s : State)
    (budget n : Nat) :
    (limbRun H budget (globalCursor H s n)).1 =
      wordTrace H s (eval (streamAnswer H s) (scan budget n)).1 := by
  induction budget generalizing n with
  | zero => rfl
  | succ budget ih =>
      have hm := stream_mask H s n
      cases ha : streamAnswer H s n with
      | none =>
          have hw : masked 31 (streamWord H s n) = modulus := by
            rw [ha] at hm
            exact hm.symm
          simp only [limbRun, read_stream, read_stream_calls, hw, modulus, if_true,
            scan, eval, ha, wordTrace_cons]
          rw [ih]
      | some a =>
          have hw : masked 31 (streamWord H s n) = a.val := by
            rw [ha] at hm
            exact hm.symm
          have hne : a.val ≠ 2147483647 := by
            have := a.isLt
            change a.val < 2147483647 at this
            omega
          simp only [limbRun, read_stream, read_stream_calls, hw, hne, if_false,
            scan, eval, ha, wordTrace, List.flatMap_cons, List.flatMap_nil, List.append_nil]

theorem wordTrace_append (H : DuplexFrames.Bytes → State) (s : State)
    (left right : List (Nat × Option (Fin modulus))) :
    wordTrace H s (left++right) = wordTrace H s left ++ wordTrace H s right := by
  exact List.flatMap_append

def sourceLimbsView (H : DuplexFrames.Bytes → State) (budget : Nat) :
    Nat → Cursor → View DuplexFrames.Bytes State (Option (List Nat) × Cursor)
  | 0, c => ([],(some [], c))
  | count+1, c =>
      let first := limbRun H budget c
      match first.2.1 with
      | none => (first.1,(none, first.2.2))
      | some a =>
          let tail := sourceLimbsView H budget count first.2.2
          (first.1++tail.1,(tail.2.1.map (a::·),tail.2.2))

theorem sourceLimbsView_exact (H : DuplexFrames.Bytes → State) (count : Nat) (c : Cursor) :
    limbsRun H count c = sourceLimbsView H 8 count c := by
  induction count generalizing c with
  | zero => rfl
  | succ count ih =>
      simp only [limbsRun, sourceLimbsView]
      cases h : (limbRun H 8 c).2.1 with
      | none => rfl
      | some a => simp only [ih]

theorem eval_limbs_succ_trace (answer : Nat → Option (Fin modulus))
    (budget count n : Nat) :
    (eval answer (limbs budget (count+1) n)).1 =
      let first := eval answer (scan budget n)
      first.1 ++ match first.2.1 with
        | none => []
        | some _ => (eval answer (limbs budget count first.2.2)).1 := by
  rw [limbs, eval_bind]
  cases h : eval answer (scan budget n) with
  | mk trace result =>
      cases result with
      | mk head next =>
          cases head with
          | none => rfl
          | some a => simp only [eval_bind, eval, List.append_nil]

theorem sourceLimbsView_stream_trace (H : DuplexFrames.Bytes → State) (s : State)
    (budget count n : Nat) :
    (sourceLimbsView H budget count (globalCursor H s n)).1 =
      wordTrace H s (eval (streamAnswer H s) (limbs budget count n)).1 := by
  induction count generalizing n with
  | zero => rfl
  | succ count ih =>
      have hs := scan_stream H s budget n
      have htrace := scan_stream_trace H s budget n
      rw [eval_limbs_succ_trace, wordTrace_append]
      simp only [sourceLimbsView, hs, htrace]
      cases hr : eval (streamAnswer H s) (scan budget n) with
      | mk trace result =>
          cases result with
          | mk head next =>
              cases head with
              | none => simp only [Option.map_none, wordTrace, List.flatMap_nil, List.append_nil]
              | some a => simp only [Option.map_some, ih]

theorem limbs_stream_trace (H : DuplexFrames.Bytes → State) (s : State)
    (count n : Nat) :
    (limbsRun H count (globalCursor H s n)).1 =
      wordTrace H s (eval (streamAnswer H s) (limbs 8 count n)).1 := by
  rw [sourceLimbsView_exact]
  exact sourceLimbsView_stream_trace H s 8 count n

#print axioms wordTrace_append
#print axioms sourceLimbsView_exact
#print axioms eval_limbs_succ_trace
#print axioms sourceLimbsView_stream_trace
#print axioms limbs_stream_trace
#print axioms read_stream_calls
#print axioms wordTrace_cons
#print axioms scan_stream_trace
end AspisV8R19.R583SamplerWordTrace
