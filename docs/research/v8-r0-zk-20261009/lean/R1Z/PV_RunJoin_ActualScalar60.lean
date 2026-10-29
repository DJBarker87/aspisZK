import R1Z.PV_RunJoin_ActualRun59
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ActualScalar60
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_NativeControl55 (Phase)
open PV_RunJoin_ActualData59
variable [ExternalTypes] [ExternalFuns]

theorem raw_roundtrip (w : aspis_core.field.wide_exact.WideExact) :
    ProverRwDictionaryTower.fromW (ProverCommitWideOps48.source (rawW w))=w := by
  cases w
  rfl

theorem prepared (phase : Phase) (p : prover.PreparedOpening)
    (hp : prover.prepare_opening .S2 phase.hash phase.backend phase.sem=ok (.Ok p)) :
    ProverRwDictionaryTower.fromW (ProverCommitWideOps48.source (data phase).g)=p.gamma ∧
    ProverRwDictionaryTower.fromW (ProverCommitWideOps48.source (data phase).k)=p.kappa ∧
    ProverRwDictionaryTower.fromW (ProverCommitWideOps48.source (data phase).a)=p.alpha0 := by
  simp only [data,preparedField,PV_RunJoin_ActualRunSources59.prepare,hp,raw_roundtrip,and_self]

theorem openings (phase : Phase) :
    ProverCommitWideOps48.value (data phase).g=(data phase).ch.opening 0 ∧
    ProverCommitWideOps48.value (data phase).k=(data phase).ch.opening 1 ∧
    ProverCommitWideOps48.value (data phase).a=(data phase).ch.opening 2 ∧
    ProverCommitWideOps48.value (data phase).b=(data phase).ch.opening 3 := ⟨rfl,rfl,rfl,rfl⟩

#print axioms raw_roundtrip
#print axioms prepared
#print axioms openings
end R1Z.PV_RunJoin_ActualScalar60
