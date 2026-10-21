import OraclePortRefineJoinStrict
import OraclePortFrozenOrderProbability

/-! Exact accepted observations. The annotated field deliberately covers both
passes and their enriched output. A raw one-pass implication alone does not
silently supply this field. All rejecting runs remain unconstrained. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortFrozenOrderJoin
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open OraclePortStoredExperimentC4 OraclePortStoredAdmissionC4 OraclePortFrozenOrderConsumer
open OraclePortRuntimeBindingC7
attribute [local instance] Classical.propDecidable

/-- Same ordered read/answer sequence and Bool on each accepted call. -/
def AcceptedVerifierJoin (source model : Verifier) : Prop :=
  ∀ H i, (eval H (source i)).2 = true → eval H (source i) = eval H (model i)

/-- Complete accepted runs, including the two-pass annotation compiler.
Equality includes public data, stored bytes, proof/words, verdict and log. -/
structure AcceptedRunJoin (D : LiteralByteProtocol.Decoder) (rust : Verifier) : Prop where
  verifier : AcceptedVerifierJoin rust (verifier D OraclePortFrozenOrder.dV_frozen)
  annotated : ∀ (P : Prover) H,
    (eval H (annotatedWith D rust P)).2.2 = true →
      eval H (annotatedWith D rust P) =
        eval H (annotated D OraclePortFrozenOrder.dV_frozen P)

theorem originalWith_eval (rust : Verifier) (P : Prover) (H : Bytes → State) :
    eval H (originalWith rust P) =
      ((eval H P).1 ++ (eval H (rust (eval H P).2)).1,
        ((eval H P).2,(eval H (rust (eval H P).2)).2)) := by
  simp only [originalWith,eval_bind,eval,List.append_nil]

theorem annotatedWith_eval (D : LiteralByteProtocol.Decoder) (rust : Verifier)
    (P : Prover) (H : Bytes → State) :
    eval H (annotatedWith D rust P) =
      let v := eval H (originalWith rust P)
      let i := enrich (build D (view v)) v.2.1
      (v.1 ++ (eval H (rust i)).1,(i,(eval H (rust i)).2)) := by
  simp only [annotatedWith,originalWith,eval_bind,OracleProgramRecording.eval_record,
    eval,List.append_nil]

/-- A sufficient, separately proved lifting rule. Stability only concerns the
verdict under enrichment; accepted logs follow from the raw join itself. -/
theorem acceptedRunJoin_of_stable (D : LiteralByteProtocol.Decoder) (rust : Verifier)
    (h : AcceptedVerifierJoin rust (verifier D OraclePortFrozenOrder.dV_frozen))
    (stable : ∀ w i H, (eval H (rust (enrich w i))).2 = (eval H (rust i)).2) :
    AcceptedRunJoin D rust := by
  refine ⟨h,?_⟩
  intro P H ha
  have before : (eval H (originalWith rust P)).2.2 = true := by
    simpa only [annotatedWith_eval,stable,originalWith_eval] using ha
  have raw : eval H (originalWith rust P) =
      eval H (originalWith (verifier D OraclePortFrozenOrder.dV_frozen) P) := by
    rw [originalWith_eval] at before
    simp only [originalWith_eval,h H (eval H P).2 before]
  rw [annotatedWith_eval,raw] at ha ⊢
  have second := h H _ ha
  change _ = eval H (annotatedWith D (verifier D OraclePortFrozenOrder.dV_frozen) P)
  simp only [annotatedWith_eval,second]

theorem total_join_accepted (D : LiteralByteProtocol.Decoder) (rust : Verifier)
    (h : ∀ i, rust i = verifier D OraclePortFrozenOrder.dV_frozen i) :
    AcceptedRunJoin D rust := by
  apply acceptedRunJoin_of_stable
  · intro H i ha; rw [h i]
  · intro w i H; rw [h _,h _,verifier_enrich]

#print axioms originalWith_eval
#print axioms annotatedWith_eval
#print axioms acceptedRunJoin_of_stable
#print axioms total_join_accepted
end AspisR1.OraclePortFrozenOrderJoin
end
