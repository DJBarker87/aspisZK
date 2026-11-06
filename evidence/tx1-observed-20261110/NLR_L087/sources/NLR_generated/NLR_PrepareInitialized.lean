import NLR_PrepareComplete
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLR_PrepareInitialized
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open AspisR1PublicPreparation.PreparedHashCode (run)
/-- Internally produced source occurrences for the SAME adopted body. There
is no supplied endpoint, event list, successful child or native realization. -/
theorem source (cfg : NLJ_Prepare.Configuration) {H : Type} (i : NLJ_Prepare.Input H) :
 ∃ events, NLJ_Prepare.Invocation cfg 12 (NLJ_Prepare.initial i)
  (run (SdkD_PrepareSource.code cfg.base cfg.boundaries cfg.std
    i.digest i.publicValue i.proof i.hash i.scratch)).2
  (run (SdkD_PrepareSource.code cfg.base cfg.boundaries cfg.std
    i.digest i.publicValue i.proof i.hash i.scratch)).1 events := by
 have actual := NLR_PrepareComplete.invocation cfg 12 (NLJ_Prepare.initial i)
  (by change 12≤12;decide)
 have equality := NLR_Prepare.source cfg i
 unfold NLJ_Prepare.SourceEquality at equality
 rw [equality] at actual
 exact actual
#print axioms source
set_option pp.proofs false
#print source
end AspisR1.NLR_PrepareInitialized
end
