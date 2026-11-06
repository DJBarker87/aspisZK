import NLR_PrepareFinalSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLR_Prepare
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open AspisR1PublicPreparation.PreparedHashCode (run)
/-- Source fold with COMPLETE outcomes/effects; conditional source heads are
kept explicit. These are NOT native-cut certificates and this is NOT a root. -/
theorem source_fold (cfg : NLJ_Prepare.Configuration) {H : Type}
 (i : NLJ_Prepare.Input H) (out : Result NLJ_Prepare.Out)
 (log : AspisR1PublicPreparation.PreparedHashCode.Log) (events : List NLJ_Prepare.Event)
 (cuts : NLJ_Prepare.Invocation cfg 12 (NLJ_Prepare.initial i) out log events) :
 run (SdkD_PrepareSource.code cfg.base cfg.boundaries cfg.std
  i.digest i.publicValue i.proof i.hash i.scratch) = (log,out) := by
 rw [←source cfg i]
 exact NLJ_Prepare.fold_from_steps cfg cuts
#print axioms source_fold
set_option pp.proofs false
#print source_fold
end AspisR1.NLR_Prepare
end
