import NNQ_Sdk
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNQ_HostDigest
open Aeneas Aeneas.Std Result

theorem observe_op43 {A : Type} (S : AdapterRw.Ops)
    (o : AdapterRw.SolanaDigest → Slice (Slice U8) → Result (Array U8 32#usize))
    (id : S2W_ExtractionBoundary.Program) (out : GExq_AccountExperiment.Outcome A) :
    Hiq_ByteSelection.select {S with op43 := o} id out = Hiq_ByteSelection.select S id out := by
  unfold Hiq_ByteSelection.select Hiq_ByteSelection.account Hiq_ByteSelection.public2
  rfl
#print axioms observe_op43
end AspisR1.NNQ_HostDigest
end
