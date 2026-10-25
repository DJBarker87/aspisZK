import F3J_SamplerCompose
import F3J_SamplerStructure
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3J_PrefixWitness
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

theorem pack (H : Bytes → State) (code : Program Bytes State LiteralTranscript.Prefix)
    (log : List (Bytes × State)) (predicate : LiteralTranscript.Prefix → Prop)
    (logs : (eval H code).1=log) (value : predicate (eval H code).2) :
    ∃ out,eval H code=(log,out) ∧ predicate out :=
  ⟨(eval H code).2,Prod.ext logs rfl,value⟩

theorem through (H : Bytes → State) (pf : RawCutProverCompiler.Proof)
    (row a b : Nat) (P middle last : LiteralTranscript.Prefix)
    (left right : List (Bytes × State))
    (first : eval H (F3J_SamplerRun.program pf row a P)=(left,middle))
    (second : eval H (F3J_SamplerRun.program pf (row+a) b middle)=(right,last)) :
    eval H (F3J_SamplerRun.program pf row (a+b) P)=(left++right,last) := by
  rw [F3J_SamplerRun.split]
  simp only [eval_bind,first,second]

theorem carried_statement (H : Bytes → State) (pf : RawCutProverCompiler.Proof)
    (row n : Nat) (P out : LiteralTranscript.Prefix) (log : List (Bytes × State))
    (success : eval H (F3J_SamplerRun.program pf row n P)=(log,out)) : out.statement=P.statement := by
  have preserved := F3J_SamplerStructure.statement H pf row n P
  rw [success] at preserved
  exact preserved

#print axioms pack
#print axioms through
#print axioms carried_statement
end AspisR1.F3J_PrefixWitness
end
