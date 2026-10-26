import F3T_Charged
import F3T_Canon
import OraclePortRefineJoinExtractionTransport
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3T_TwoPass
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open F3T_Experiment F3T_Charged
abbrev Verifier := F3_Model.Input → Program Bytes State Bool

def originalWith (rust : Verifier) (P : Prover) : Program Bytes State (F3_Model.Input × Bool) :=
  bind P fun i => bind (rust i) fun b => .done (i,b)

def compiledWith (D : LiteralByteProtocol.Decoder) (rust : Verifier) (P : Prover) : Prover :=
  bind (OracleProgramRecording.record (originalWith rust P)) fun v =>
    .done (enrich (build D (view v)) v.2.1)

abbrev annotatedWith (D : LiteralByteProtocol.Decoder) (rust : Verifier) (P : Prover) :=
  originalWith rust (compiledWith D rust P)

/-- This is an explicit unproved source-refinement obligation, not an instance. -/
def RawJoin (D : LiteralByteProtocol.Decoder) (rust : Verifier) : Prop :=
  ∀ H i, (eval H (rust i)).2=true → eval H (rust i)=eval H (F3_Model.verifier D i)

/-- Annotation must not change the source's physical input or its execution. -/
def AnnotationInvariant (rust : Verifier) : Prop :=
  ∀ w i, rust (enrich w i)=rust i

theorem original_eval (rust : Verifier) (P : Prover) (H : Bytes → State) :
    eval H (originalWith rust P)=
      ((eval H P).1 ++ (eval H (rust (eval H P).2)).1,
        ((eval H P).2,(eval H (rust (eval H P).2)).2)) := by
  simp only [originalWith,eval_bind,eval,List.append_nil]

theorem compiled_eval (D : LiteralByteProtocol.Decoder) (rust : Verifier) (P : Prover) (H : Bytes → State) :
    eval H (compiledWith D rust P)=
      let v:=eval H (originalWith rust P)
      (v.1,enrich (build D (view v)) v.2.1) := by
  simp only [compiledWith,eval_bind,OracleProgramRecording.eval_record,eval,List.append_nil]

theorem annotated_eval (D : LiteralByteProtocol.Decoder) (rust : Verifier)
    (inv : AnnotationInvariant rust) (P : Prover) (H : Bytes → State) :
    eval H (annotatedWith D rust P)=
      let v:=eval H (originalWith rust P)
      (v.1 ++ (eval H (rust v.2.1)).1,
        (enrich (build D (view v)) v.2.1,v.2.2)) := by
  rw [annotatedWith,original_eval,compiled_eval]
  dsimp only
  rw [inv]
  have same : (eval H (rust (eval H (originalWith rust P)).2.1)).2=
      (eval H (originalWith rust P)).2.2 := by rw [original_eval]
  rw [same]

#print axioms original_eval
#print axioms compiled_eval
#print axioms annotated_eval
end AspisR1.F3T_TwoPass
end
