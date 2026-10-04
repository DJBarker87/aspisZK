import AspisV8R19.R583SamplerWordTrace
import AspisV8R19.AdaptiveFirstReadLaw

set_option autoImplicit false
namespace AspisV8R19.R584IndependentBlockSampler
open MemoizedProgramLaw OracleProgramOps AdaptiveFirstReadLaw OracleResampling
open QM31SamplerProgram SourceDuplexStep SourceOraclePrograms SamplerWords

structure BlockCursor where
  block : State
  index : Fin 9

def project (c : Cursor) : BlockCursor := ⟨c.block,c.index⟩

noncomputable def outputMean {I A O : Type} [Fintype A]
    (program : Program I A O) (observe : O → ℚ) : ℚ :=
  independentMean program (fun v => observe v.2)

theorem outputMean_bind {I A O R : Type} [Fintype A]
    (program : Program I A O) (next : O → Program I A R) (observe : R → ℚ) :
    outputMean (bind program next) observe =
      outputMean program (fun o => outputMean (next o) observe) := by
  unfold outputMean
  rw [independentMean_bind]

def readBlockProgram (c : BlockCursor) : Program Unit State (Nat × BlockCursor) :=
  if h : c.index.val=8 then
    .ask () (fun block => .done (word block 0,⟨block,1⟩))
  else .done (word c.block ⟨c.index.val,by have := c.index.isLt; omega⟩,
    ⟨c.block,⟨c.index.val+1,by have := c.index.isLt; omega⟩⟩)

def limbBlockProgram : Nat → BlockCursor → Program Unit State (Option Nat × BlockCursor)
  | 0,c => .done (none,c)
  | n+1,c => bind (readBlockProgram c) (fun r =>
      if masked 31 r.1=2147483647 then limbBlockProgram n r.2
      else .done (some (masked 31 r.1),r.2))

def limbsBlockProgram : Nat → BlockCursor → Program Unit State (Option (List Nat) × BlockCursor)
  | 0,c => .done (some [],c)
  | n+1,c => bind (limbBlockProgram 8 c) (fun r => match r.1 with
      | none => .done (none,r.2)
      | some a => bind (limbsBlockProgram n r.2) (fun tail =>
          .done (tail.1.map (a::·),tail.2)))

def challengeBlockProgram : Program Unit State (Option (List Nat) × BlockCursor) :=
  .ask () (fun block => limbsBlockProgram 4 ⟨block,0⟩)

theorem limb_independent_block (budget : Nat) (c : Cursor)
    (observe : Option Nat × BlockCursor → ℚ) :
    outputMean (limbProgram budget c) (fun r => observe (r.1,project r.2)) =
      outputMean (limbBlockProgram budget (project c)) observe := by
  induction budget generalizing c with
  | zero => rfl
  | succ budget ih =>
      simp only [limbProgram, limbBlockProgram, outputMean_bind]
      by_cases hi : c.index.val=8
      · simp only [readProgram, readBlockProgram, project, hi, ↓reduceDIte,
          squeezeProgram, OracleProgramOps.bind, outputMean, independentMean]
        apply mean_congr
        intro block
        have hconst : ∀ next : State,
            independentMean
              (if masked 31 (word block 0)=2147483647 then
                limbProgram budget ⟨next,block,1⟩
              else .done (some (masked 31 (word block 0)),⟨next,block,1⟩))
              (fun r => observe (r.2.1,project r.2.2)) =
            outputMean
              (if masked 31 (word block 0)=2147483647 then
                limbBlockProgram budget ⟨block,1⟩
              else .done (some (masked 31 (word block 0)),⟨block,1⟩)) observe := by
          intro next
          split
          · exact ih ⟨next,block,1⟩
          · rfl
        simp only [project, outputMean] at hconst
        rw [mean_congr hconst, mean_const]
      · simp only [readProgram, readBlockProgram, project, hi, ↓reduceDIte,
          outputMean, independentMean]
        split
        · exact ih _
        · rfl

theorem outputMean_congr {I A O : Type} [Fintype A]
    (program : Program I A O) {f g : O → ℚ} (h : ∀ o, f o=g o) :
    outputMean program f = outputMean program g := by
  exact R572SequentialWordMass.independentMean_congr program (fun v => h v.2)

theorem limbs_independent_block (count : Nat) (c : Cursor)
    (observe : Option (List Nat) × BlockCursor → ℚ) :
    outputMean (limbsProgram count c) (fun r => observe (r.1,project r.2)) =
      outputMean (limbsBlockProgram count (project c)) observe := by
  induction count generalizing c observe with
  | zero => rfl
  | succ count ih =>
      let nextObserve : Option Nat × BlockCursor → ℚ := fun first =>
        match first.1 with
        | none => observe (none,first.2)
        | some a => outputMean (limbsBlockProgram count first.2)
            (fun tail => observe (tail.1.map (a::·),tail.2))
      have hnext : ∀ first : Option Nat × Cursor,
          outputMean
            (match first.1 with
            | none => .done (none,first.2)
            | some a => bind (limbsProgram count first.2)
                (fun tail => .done (tail.1.map (a::·),tail.2)))
            (fun r => observe (r.1,project r.2)) =
          nextObserve (first.1,project first.2) := by
        intro first
        cases first with
        | mk head next =>
            cases head with
            | none => rfl
            | some a =>
                simp only [nextObserve, outputMean_bind]
                change outputMean (limbsProgram count next)
                  (fun tail => observe (tail.1.map (a::·),project tail.2)) = _
                exact ih next (fun tail => observe (tail.1.map (a::·),tail.2))
      rw [limbsProgram, outputMean_bind]
      rw [outputMean_congr (limbProgram 8 c) hnext]
      rw [limb_independent_block]
      simp only [limbsBlockProgram, outputMean_bind]
      apply outputMean_congr
      intro first
      cases first with
      | mk head next =>
          cases head with
          | none => rfl
          | some a => simp only [nextObserve, outputMean_bind]; rfl

#print axioms outputMean_congr
#print axioms limbs_independent_block
#print axioms outputMean_bind
#print axioms limb_independent_block
end AspisV8R19.R584IndependentBlockSampler
