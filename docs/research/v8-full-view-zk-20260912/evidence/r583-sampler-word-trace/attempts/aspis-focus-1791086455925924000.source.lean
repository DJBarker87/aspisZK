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

#print axioms read_stream_calls
#print axioms wordTrace_cons
#print axioms scan_stream_trace
end AspisV8R19.R583SamplerWordTrace
