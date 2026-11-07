import LIBB_AccountCarriers
import LIBB_V1DecoderValues
set_option autoImplicit false
noncomputable section
namespace LIBB_AccountGraph
open Aeneas Aeneas.Std
open LIBB_V1DecoderValues (asOption)
/-- Project the decoder error only at its Option-valued caller boundary. -/
theorem tail_option {A B F : Type} (f : A → B) (r : core.result.Result A F) :
 asOption f (NKF_BoxModel.tail r) = asOption f r := by cases r <;> rfl

theorem project {A B F : Type} (f : A → B)
 (raw : Result (core.result.Result A F))
 (decoded : core.result.Result A AdapterRw.solana_program_error.ProgramError)
 (h : NJQ_Canonical.mapOuter NKF_BoxModel.tail raw = .ok decoded) :
 LIBB_ResultTotal.mapOuter (asOption f) raw = .ok (asOption f decoded) := by
 cases raw with
 | fail e => cases h
 | div => cases h
 | ok r =>
   exact congrArg Result.ok ((tail_option f r).symm.trans
     (congrArg (asOption f) (Result.ok.inj h)))

theorem master_same (b : Slice U8) :
 LIBB_AccountDecoderReuse.master (NND_Carrier.bytes b) =
 asOption NND_Carrier.master (NMX_MasterValue.decoded b) := by
 calc
  _ = NMX_R2_DecoderLibrary.master (NMX_R2_Carrier.bytes b) :=
    congrArg NMX_R2_DecoderLibrary.master (LIBB_AccountCarriers.bytes b).symm
  _ = asOption NMX_R2_Carrier.master (NMX_MasterValue.decoded b) :=
    NMX_R2_DecoderLibrary.master_same b
  _ = _ := congrArg (fun f => asOption f (NMX_MasterValue.decoded b))
    (funext LIBB_AccountCarriers.master)

theorem checkpoint_same (b : Slice U8) :
 LIBB_AccountDecoderReuse.checkpoint (NND_Carrier.bytes b) =
 asOption NND_Carrier.checkpoint (NMX_CheckpointValue.decoded b) := by
 calc
  _ = NMX_R2_DecoderLibrary.checkpoint (NMX_R2_Carrier.bytes b) :=
    congrArg NMX_R2_DecoderLibrary.checkpoint (LIBB_AccountCarriers.bytes b).symm
  _ = asOption NMX_R2_Carrier.checkpoint (NMX_CheckpointValue.decoded b) :=
    NMX_R2_DecoderLibrary.checkpoint_same b
  _ = _ := congrArg (fun f => asOption f (NMX_CheckpointValue.decoded b))
    (funext LIBB_AccountCarriers.checkpoint)

theorem master_model (b : Slice U8) :
 LIBB_ResultTotal.mapOuter (asOption NND_Carrier.master) (NJQ_Canonical.master b) =
 .ok (LIBB_AccountDecoderReuse.master (NND_Carrier.bytes b)) :=
 (project NND_Carrier.master _ _ (NMX_MasterValue.source b)).trans
  (congrArg Result.ok (master_same b).symm)

theorem checkpoint_model (b : Slice U8) :
 LIBB_ResultTotal.mapOuter (asOption NND_Carrier.checkpoint) (NJQ_Canonical.checkpoint b) =
 .ok (LIBB_AccountDecoderReuse.checkpoint (NND_Carrier.bytes b)) :=
 (project NND_Carrier.checkpoint _ _ (NMX_CheckpointValue.source b)).trans
  (congrArg Result.ok (checkpoint_same b).symm)
#print axioms tail_option
#print axioms project
#print axioms master_same
#print axioms checkpoint_same
#print axioms master_model
#print axioms checkpoint_model
end LIBB_AccountGraph
end
