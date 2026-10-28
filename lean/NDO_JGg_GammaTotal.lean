import RPz7_S1ClosedPreparationHashCodeV1
import GammaCandidateTotalityV14
set_option autoImplicit false
namespace AspisR1.JGg_GammaTotal
open Aeneas Aeneas.Std Result
open AspisR1ClaimPreparedBridge

theorem source (block : Array U8 32#usize) :
    ∃ out,candidateGammaPublic block=ok out := by
  obtain ⟨value,call⟩ := AspisR1GammaCaller.DigitsModel.candidate_gamma_total block
  refine ⟨gammaToPublic value,?_⟩
  unfold candidateGammaPublic
  rw [call,bind_tc_ok]
#print axioms source
end AspisR1.JGg_GammaTotal
