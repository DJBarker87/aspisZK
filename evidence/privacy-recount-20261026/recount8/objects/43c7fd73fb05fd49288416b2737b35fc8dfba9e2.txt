import R1Z.ProverRwFullExternalFuns
import R1Z.ProverRwSemanticSampler

/-! Concrete selected sampler entry in the full typed dictionary. The other
261 function entries and 27 type entries remain explicit parameters. This is
an installation of one callee, not a full native dictionary instance. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwFullSampler
open Aeneas Aeneas.Std Result ProverRwFull
abbrev SelectedQM := ProverRwSampler.aspis_core.field.QM31
abbrev CallerQM := ProverRwFull.aspis_core.field.QM31

def fromSelected (q : SelectedQM) : CallerQM :=
  ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
def toSelected (q : CallerQM) : SelectedQM :=
  ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩

theorem roundtrip (q : SelectedQM) : toSelected (fromSelected q) = q := by
  cases q with
  | mk c0 c1 => cases c0; cases c1; rfl

def selected (b : Array U8 32#usize) : Result CallerQM := do
  let q ← ProverRwSampler.sampler.qm31_sample b
  ok (fromSelected q)

@[reducible] def install [ExternalTypes] (ops : ExternalFuns) : ExternalFuns :=
  { ops with op248 := selected }

theorem entry [ExternalTypes] (ops : ExternalFuns) (b : Array U8 32#usize) :
    @ProverRwFull.sampler.qm31_sample _ (install ops) b = selected b := rfl

def decode (q : CallerQM) := ProverRwSemanticSampler.decode (toSelected q)

theorem total [ExternalTypes] (ops : ExternalFuns) (b : Array U8 32#usize) :
    ∃ q : CallerQM,
      @ProverRwFull.sampler.qm31_sample _ (install ops) b = ok q ∧
      algebraMap AspisV8R15.ExactTowerBase.QM31Exact AspisWideTower.WideExact (decode q) =
        R0P.SemSource.semChal (AspisV8R19.SqueezeOracleBridge.decodeState b) := by
  obtain ⟨q,hq,he⟩ := ProverRwSemanticSampler.sample_total_semChal b
  refine ⟨fromSelected q, ?_, ?_⟩
  · simp only [entry,selected,hq,bind_tc_ok]
  · simpa only [decode,roundtrip] using he

#print axioms roundtrip
#print axioms entry
#print axioms total
end R1Z.ProverRwFullSampler
