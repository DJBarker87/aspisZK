import AspisV8R19.Q22WordScan

/-! The selected source call has count=22, bound=2^18, max_draws=64.
Eight block iterations suffice by the proved scan progress invariant. -/
set_option autoImplicit false
namespace AspisV8R19.Q22SamplerProgram
open DuplexFrames SourceDuplexStep SourceOraclePrograms SamplerWords Q22WordScan
open MemoizedProgramLaw OracleProgramOps

abbrev Result := Except Nat (List Nat) × State

def loopProgram : Nat → State → ScanState → Program Bytes State Result
  | 0,s,q => .done (finish q,s)
  | n+1,s,q =>
      if q.draws < 64 then bind (squeezeProgram s) (fun p =>
        let r := scan q (words 18 p.1)
        if r.2 then .done (finish r.1,p.2)
        else loopProgram n p.2 r.1)
      else .done (finish q,s)

def loopRun (H : Bytes → State) : Nat → State → ScanState → View Bytes State Result
  | 0,s,q => ([],(finish q,s))
  | n+1,s,q =>
      if q.draws < 64 then
        let p := step H s
        let r := scan q (words 18 p.1)
        if r.2 then (calls H s,(finish r.1,p.2))
        else
          let tail := loopRun H n p.2 r.1
          (calls H s ++ tail.1,tail.2)
      else ([],(finish q,s))

theorem loop_exact (H : Bytes → State) (n : Nat) (s : State) (q : ScanState) :
    eval H (loopProgram n s q) = loopRun H n s q := by
  induction n generalizing s q with
  | zero => rfl
  | succ n ih =>
      by_cases hd : q.draws < 64
      · simp only [loopProgram,loopRun,if_pos hd,eval_bind,squeeze_eval]
        by_cases hs : (scan q (words 18 (step H s).1)).2 = true <;> simp [hs,eval,ih]
      · simp [loopProgram,loopRun,hd,eval]

/-- Literal source while-loop relation; there is no artificial fuel outcome. -/
inductive SourceExec (H : Bytes → State) : State → ScanState → View Bytes State Result → Prop where
  | done (s : State) (q : ScanState) (cap : 64 ≤ q.draws) :
      SourceExec H s q ([],(finish q,s))
  | stop (s : State) (q : ScanState) (draw : q.draws < 64)
      (stop : (scan q (words 18 (step H s).1)).2 = true) :
      SourceExec H s q (calls H s,(finish (scan q (words 18 (step H s).1)).1,(step H s).2))
  | more (s : State) (q : ScanState) (draw : q.draws < 64)
      (keepGoing : (scan q (words 18 (step H s).1)).2 = false)
      (tail : View Bytes State Result)
      (rest : SourceExec H (step H s).2 (scan q (words 18 (step H s).1)).1 tail) :
      SourceExec H s q (calls H s ++ tail.1,tail.2)

theorem sufficient_fuel_source_exec (H : Bytes → State) (n : Nat) (s : State) (q : ScanState)
    (enough : 64 ≤ q.draws+8*n) : SourceExec H s q (loopRun H n s q) := by
  induction n generalizing s q with
  | zero => exact .done s q (by simpa using enough)
  | succ n ih =>
      by_cases hd : q.draws < 64
      · cases hs : (scan q (words 18 (step H s).1)).2 with
        | false =>
            simp only [loopRun,if_pos hd,hs,Bool.false_eq_true,↓reduceIte]
            apply SourceExec.more s q hd hs
            apply ih
            have progress := scan_progress q (words 18 (step H s).1) hs
            rw [words_length] at progress
            omega
        | true =>
            simpa only [loopRun,if_pos hd,hs,↓reduceIte] using SourceExec.stop s q hd hs
      · simpa only [loopRun,if_neg hd] using SourceExec.done s q (by omega)

def challengeProgram (s : State) : Program Bytes State Result := loopProgram 8 s ⟨[],0⟩
def challengeRun (H : Bytes → State) (s : State) : View Bytes State Result := loopRun H 8 s ⟨[],0⟩

theorem challenge_exact (H : Bytes → State) (s : State) :
    eval H (challengeProgram s) = challengeRun H s := loop_exact H 8 s ⟨[],0⟩

theorem no_artificial_cutoff (H : Bytes → State) (s : State) :
    SourceExec H s ⟨[],0⟩ (challengeRun H s) := sufficient_fuel_source_exec H 8 s ⟨[],0⟩ (by decide)

theorem completion_detection_block (H : Bytes → State) (n : Nat) (s : State) (q : ScanState)
    (complete : q.accepted.length = 22) (remaining : q.draws < 64) :
    loopRun H (n+1) s q = (calls H s,(finish q,(step H s).2)) := by
  have nonempty : words 18 (step H s).1 ≠ [] := by
    intro h; have hh := words_length 18 (step H s).1; rw [h] at hh; cases hh
  obtain ⟨x,xs,hxs⟩ := List.exists_cons_of_ne_nil nonempty
  simp [loopRun,remaining,hxs,scan_complete q x xs complete]

#print axioms loop_exact
#print axioms sufficient_fuel_source_exec
#print axioms challenge_exact
#print axioms no_artificial_cutoff
#print axioms completion_detection_block
end AspisV8R19.Q22SamplerProgram
