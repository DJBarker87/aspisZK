import NMC_WindowModels
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMC_Cut_terminalGuard
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NMC_Window
/-- Frozen r1_semantic.rs:259. FULL segment contract: original inputs,
allocator/Reservation observation, every heap region, every scalar/array
projection and the exact Result. Still OPEN until the native projections and
same-call child/lifecycle installation establish EVERY conjunct. -/
def Contract {A : Type} (native : Context A→NLC_Finish.Q→Observation A NMC_Models.Reply) : Prop :=
 Cut native NMC_Models.terminalGuard
/-- Forward G transport only. This conditional lemma is not a136 root,
not a full parent fold, and not a claim that partial Kani windows prove Cut. -/
theorem forward {A : Type} (native : Context A→NLC_Finish.Q→Observation A NMC_Models.Reply)
 (cut : Contract native) (before : Context A) (args : NLC_Finish.Q) :
 native before args=NMC_Models.terminalGuard before args :=
 NMC_Window.from_windows native NMC_Models.terminalGuard cut before args
#print axioms forward
set_option pp.proofs false in #print Contract
set_option pp.proofs false in #print forward
end AspisR1.NMC_Cut_terminalGuard
end
