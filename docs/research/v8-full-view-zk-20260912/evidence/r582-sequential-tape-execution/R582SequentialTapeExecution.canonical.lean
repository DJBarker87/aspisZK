import AspisV8R19.R580SourceWordStream

set_option autoImplicit false
namespace AspisV8R19.R582SequentialTapeExecution
open MemoizedProgramLaw OracleProgramOps R572SequentialWordMass R578FiniteWordTape
open R443BoundedRejectionMass
variable {p : Nat} {O R : Type}

/-- Every actual read uses the current cursor; every returned cursor is the
number of consumed words. Both successful and failed results are retained. -/
def Sequential : Nat → Program Nat (Option (Fin p)) (O × Nat) → Prop
  | cursor, .done output => output.2 = cursor
  | cursor, .ask i next => i = cursor ∧ ∀ a, Sequential (cursor+1) (next a)

theorem sequential_bind (cursor : Nat)
    (program : Program Nat (Option (Fin p)) (O × Nat))
    (next : O × Nat → Program Nat (Option (Fin p)) (R × Nat))
    (hs : Sequential cursor program) (hn : ∀ output, Sequential output.2 (next output)) :
    Sequential cursor (bind program next) := by
  induction program generalizing cursor with
  | done output =>
      change output.2 = cursor at hs
      change Sequential cursor (next output)
      rw [← hs]
      exact hn output
  | ask i k ih =>
      exact ⟨hs.1, fun a => ih a (cursor+1) (hs.2 a)⟩

theorem scan_sequential (budget cursor : Nat) :
    Sequential cursor (scan (p := p) budget cursor) := by
  induction budget generalizing cursor with
  | zero => rfl
  | succ budget ih =>
      refine ⟨rfl, ?_⟩
      intro a
      cases a with
      | none => exact ih (cursor+1)
      | some a => rfl

theorem limbs_sequential (budget count cursor : Nat) :
    Sequential cursor (limbs (p := p) budget count cursor) := by
  induction count generalizing cursor with
  | zero => rfl
  | succ count ih =>
      apply sequential_bind cursor _ _ (scan_sequential budget cursor)
      intro first
      cases first with
      | mk head next =>
          cases head with
          | none => rfl
          | some a =>
              apply sequential_bind next _ _ (ih next)
              intro tail
              cases tail with
              | mk result stop => cases result <;> rfl

theorem runTape_eval (fuel cursor : Nat)
    (program : Program Nat (Option (Fin p)) (O × Nat))
    (hs : Sequential cursor program) (hb : Bounded fuel program)
    (tape : Tape p fuel) (answer : Nat → Option (Fin p))
    (agree : ∀ i : Fin fuel, tape i = answer (cursor+i.val)) :
    runTape fuel program tape = some (eval answer program) := by
  induction fuel generalizing cursor program with
  | zero =>
      cases program with
      | done output => rfl
      | ask i next => exact False.elim hb
  | succ fuel ih =>
      cases program with
      | done output => rfl
      | ask i next =>
          have hfirst : tape 0 = answer i := by simpa only [Fin.val_zero, Nat.add_zero, hs.1] using agree 0
          have htail : ∀ j : Fin fuel, tape j.succ = answer ((cursor+1)+j.val) := by
            intro j
            simpa only [Fin.val_succ, Nat.add_assoc, Nat.add_comm 1 j.val] using agree j.succ
          have hrec := ih (cursor+1) (next (tape 0)) (hs.2 (tape 0)) (hb (tape 0))
            (fun j => tape j.succ) htail
          rw [hfirst] at hrec
          simp only [runTape, hfirst, hrec, Option.map_some, eval]

open R580SourceWordStream R579FourBlockTape SourceDuplexStep QM31SamplerProgram
open R442RejectionAlphabet R445InitialBlockRejectionLaw

noncomputable def sourceBlocks (H : DuplexFrames.Bytes → State) (s : State) : Blocks :=
  fun i => blockSeq H s i.val

theorem source_blockTape_agree (H : DuplexFrames.Bytes → State) (s : State) (i : Fin 32) :
    blockTape (sourceBlocks H s) i = streamAnswer H s i.val := by
  apply (alphabetEquiv modulus).symm.injective
  apply Fin.ext
  rw [blockTape_value, stream_mask]
  rfl

theorem source_word_tape (H : DuplexFrames.Bytes → State) (s : State) :
    runTape 32 (limbs 8 4 0) (blockTape (sourceBlocks H s)) =
      some (eval (streamAnswer H s) (limbs 8 4 0)) := by
  apply runTape_eval 32 0 _ (limbs_sequential 8 4 0) (limbs_bounded 8 4 0)
  intro i
  simpa only [Nat.zero_add] using source_blockTape_agree H s i

theorem source_challenge_result_tape (H : DuplexFrames.Bytes → State) (s : State) :
    some (challengeRun H s).2.1 =
      (runTape 32 (limbs 8 4 0) (blockTape (sourceBlocks H s))).map
        (fun v => v.2.1.map (List.map Fin.val)) := by
  rw [source_word_tape, Option.map_some, challenge_stream]

theorem source_challenge_state_tape (H : DuplexFrames.Bytes → State) (s : State) :
    some (challengeRun H s).2 =
      (runTape 32 (limbs 8 4 0) (blockTape (sourceBlocks H s))).map
        (fun v => (v.2.1.map (List.map Fin.val),(globalCursor H s v.2.2).state)) := by
  rw [source_word_tape, Option.map_some, challenge_stream]

#print axioms source_challenge_state_tape
#print axioms source_blockTape_agree
#print axioms source_word_tape
#print axioms source_challenge_result_tape
#print axioms sequential_bind
#print axioms scan_sequential
#print axioms limbs_sequential
#print axioms runTape_eval
end AspisV8R19.R582SequentialTapeExecution
