import R1Z.PV_CB_CanonicalTower
import R1Z.ProverRwFullSampler
set_option autoImplicit false
namespace R1Z.PV_CB_CanonicalSampler
open Aeneas Aeneas.Std Result ProverRwFull

/-- Canonicality is produced by the retained selected sampler for every block;
    no canonicality or desired sampler result is assumed. Native/source
    association of the complete circle wrapper is still separate. -/
theorem selected (block : Array U8 32#usize) :
    ∃ q, ProverRwFullSampler.selected block = ok q ∧ PV_CB_CanonicalTower.Valid q := by
  obtain ⟨q,hq,hcanonical,_⟩ := ProverRwSamplerModel.sample_total block
  refine ⟨ProverRwFullSampler.fromSelected q,?_,?_⟩
  · simp only [ProverRwFullSampler.selected,hq,bind_tc_ok]
  · exact hcanonical

theorem installed [ExternalTypes] (ops : ExternalFuns) (block : Array U8 32#usize) :
    ∃ q, (ProverRwFullSampler.install ops).op248 block = ok q ∧ PV_CB_CanonicalTower.Valid q := by
  obtain ⟨q,hq,hcanonical⟩ := selected block
  exact ⟨q,hq,hcanonical⟩
#print axioms selected
#print axioms installed
end R1Z.PV_CB_CanonicalSampler
