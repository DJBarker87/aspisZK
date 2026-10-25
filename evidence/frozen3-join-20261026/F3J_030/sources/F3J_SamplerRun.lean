import F3J_InputRows
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3J_SamplerRun
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

def program (pf : RawCutProverCompiler.Proof) : Nat → Nat → LiteralTranscript.Prefix →
    Program Bytes State LiteralTranscript.Prefix
  | _,0,P => .done P
  | row,n+1,P => bind (LiteralByteSampler.samp row P (pf row)).toProgram fun c =>
      program pf (row+1) n (P.ext (pf row) c)

theorem length (H : Bytes → State) (pf : RawCutProverCompiler.Proof)
    (row n : Nat) (P : LiteralTranscript.Prefix) :
    (eval H (program pf row n P)).2.rounds.length=P.rounds.length+n := by
  induction n generalizing row P with
  | zero => simp only [program,eval,Nat.add_zero]
  | succ n ih =>
    rw [program,eval_bind]
    simp only
    rw [ih]
    simp only [FS.Prefix.ext,List.length_append,List.length_singleton]
    omega

theorem split (H : Bytes → State) (pf : RawCutProverCompiler.Proof)
    (row a b : Nat) (P : LiteralTranscript.Prefix) :
    eval H (program pf row (a+b) P)=
      eval H (bind (program pf row a P) (program pf (row+a) b)) := by
  induction a generalizing row P with
  | zero => simp only [Nat.zero_add,Nat.add_zero,program,eval_bind,eval,List.nil_append]
  | succ a ih =>
    simp only [Nat.succ_add,program,eval_bind]
    rw [ih]
    simp only [eval_bind,List.append_assoc]
    congr 1 <;> congr 1 <;> omega

#print axioms length
#print axioms split
end AspisR1.F3J_SamplerRun
end
