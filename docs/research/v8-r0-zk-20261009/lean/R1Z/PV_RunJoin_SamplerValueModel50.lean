import R1Z.PV_RunJoin_OpeningBlock50
import R1Z.PV_RunJoin_ScalarRaw50
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SamplerValueModel50
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46 ProverCommitWideOps48

def nonzero (i : Fin 4) : Bool := decide (i=0)

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    (i : Fin 4) (b : Array U8 32#usize) :
    value (PV_RunJoin_SamplerValue49.value base heap box ops b (nonzero i))=
      PhaseSamplerParserBin.openingScalar i (PV_RunJoin_OpeningBlock50.answer b) := by
  obtain ⟨a,ha,hc,hm⟩ := PV_RunJoin_OpeningBlock50.complete base heap box ops i b
  have chosen := (PV_RunJoin_SamplerValue49.spec base heap box ops b (nonzero i)).1
  have eq : PV_RunJoin_SamplerValue49.value base heap box ops b (nonzero i)=a := by
    apply PV_RunJoin_ScalarRaw50.injective
    apply Result.ok.inj
    by_cases hi : i=0
    · simp only [nonzero,hi,decide_true,if_true] at chosen ha ⊢
      exact chosen.symm.trans ha
    · simp only [nonzero,hi,decide_false,Bool.false_eq_true,if_false] at chosen ha ⊢
      exact chosen.symm.trans ha
  rw [eq]
  exact hm
#print axioms nonzero
#print axioms complete
end R1Z.PV_RunJoin_SamplerValueModel50
