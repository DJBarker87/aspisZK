import F3K_SamplerProtocol
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3K_SamplerIndex
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

theorem old_index (H : Bytes → State) (pf : RawCutProverCompiler.Proof)
    (row n : Nat) (P : LiteralTranscript.Prefix) (j : Nat) (hj : j<P.rounds.length) :
    (eval H (F3J_SamplerRun.program pf row n P)).2.rounds[j]?=P.rounds[j]? := by
  induction n generalizing row P with
  | zero => rfl
  | succ n ih =>
    rw [F3J_SamplerStep.step]
    let next := F3K_SamplerOne.next H pf row P
    change (eval H (F3J_SamplerRun.program pf (row+1) n next)).2.rounds[j]?=_
    have hi : j<next.rounds.length := by
      change j<(P.rounds++[_]).length
      simp only [List.length_append,List.length_singleton]
      omega
    exact (ih (row+1) next hi).trans (List.getElem?_append_left hj)

theorem first_entry (H : Bytes → State) (pf : RawCutProverCompiler.Proof)
    (row n : Nat) (P : LiteralTranscript.Prefix) :
    (eval H (F3J_SamplerRun.program pf row (n+1) P)).2.rounds[P.rounds.length]?=
      some (pf row,(eval H (LiteralByteSampler.samp row P (pf row)).toProgram).2) := by
  rw [F3J_SamplerStep.step]
  let next := F3K_SamplerOne.next H pf row P
  change (eval H (F3J_SamplerRun.program pf (row+1) n next)).2.rounds[P.rounds.length]?=_
  have hi : P.rounds.length<next.rounds.length := by
    change P.rounds.length<(P.rounds++[_]).length
    simp only [List.length_append,List.length_singleton]
    omega
  rw [old_index H pf (row+1) n next P.rounds.length hi]
  change (P.rounds++[_])[P.rounds.length]?=_
  rw [List.getElem?_append_right (Nat.le_refl _),Nat.sub_self]
  rfl

#print axioms old_index
#print axioms first_entry
end AspisR1.F3K_SamplerIndex
end
