import LIB_PoolCarriers
import LIB_PolicyValue
import LIB_V1DecoderValues
import LIB_V2DecoderValues
import NJY_Roots
import NHY_RegistryJoin
import NIS_EntryJoin
set_option autoImplicit false
noncomputable section
namespace LIB_PoolRegistry
open Aeneas Aeneas.Std NND_Carrier LIB_V1DecoderValues
abbrev validatePolicy := LIB_PolicyValue.validate
abbrev decodeRegistryV1 := LIB_V1DecoderValues.registry
abbrev decodeRegistryV2 := LIB_V2DecoderValues.registry
abbrev decodeEntryV1 := LIB_V1DecoderValues.entry
abbrev decodeEntryV2 := LIB_V2DecoderValues.entry
/-- CLOSED policy supplier, at the actual deployed slot and SAME policy. -/
theorem policy_root {E : Type} (missing : AspisR1.IDa_Deployed.Uninstalled E)
    (devnet : Bool) (indexError : E) (reservation : AspisR1.NP6_StdModel.Reservation)
    (p : NHY_PolicyModel.Policy) :
    LIB_ResultTotal.mapOuter LIB_PolicyValue.isOk
      ((NHJ_DeployedIds.configuration (NHY_PolicyModel.bindPolicy missing)
        devnet indexError reservation).adapter.op15 p) =
    .ok (validatePolicy (policy p)) := by
  rw [NHY_PolicyModel.actual_slot]
  exact LIB_PolicyValue.native p
/-- Deterministic graph of CLOSED TX2:203's model, never the image of Cut. -/
theorem registry1_model (b : Slice U8) :
    LIB_ResultTotal.mapOuter (asOption registryV1)
      (NJQ_Canonical.mapOuter NJQ_Canonical.registryResult (NJY_Registry.model b)) =
    .ok (decodeRegistryV1 (bytes b)) := LIB_V1DecoderValues.registry_result b
theorem entry1_model (b : Slice U8) :
    LIB_ResultTotal.mapOuter (asOption entryV1)
      (NJQ_Canonical.mapOuter NJQ_Canonical.entryResult (NJY_Entry.model b)) =
    .ok (decodeEntryV1 (bytes b)) := LIB_V1DecoderValues.entry_result b
/-- The supplied CLOSED root is composed at exactly b, log and out. -/
theorem registry1_root (b : Slice U8) (log : Option NJI_V1Carrier.R)
    (out : core.result.Result NJI_V1Carrier.R NJI_V1Carrier.F)
    (cut : NJY_Registry.Cut b log out) :
    asOption registryV1 (NJQ_Canonical.registryResult out) = decodeRegistryV1 (bytes b) := by
  have h := registry1_model b
  rw [←NJY_Roots.registry b log out cut] at h
  exact Result.ok.inj h
theorem entry1_root (b : Slice U8) (log : Option NJI_V1Carrier.E)
    (out : core.result.Result NJI_V1Carrier.E NJI_V1Carrier.F)
    (cut : NJY_Entry.Cut b log out) :
    asOption entryV1 (NJQ_Canonical.entryResult out) = decodeEntryV1 (bytes b) := by
  have h := entry1_model b
  rw [←NJY_Roots.entry b log out cut] at h
  exact Result.ok.inj h
/-- Bind the V2 graph directly to its CLOSED cohort model equation. -/
theorem registry2_root (base : AdapterRw.Ops) (b : Slice U8) :
    LIB_ResultTotal.mapOuter (asOption registryV2)
      (do let reply ← NHY_RegistryModel.body b
          Result.ok (NCX_Install.mapReturn NCX_Carrier.registry reply)) =
    .ok (decodeRegistryV2 (bytes b)) := by
  rw [←NHY_RegistryJoin.cohort base b]
  exact LIB_V2DecoderValues.registry_result b
theorem entry2_root (base : AdapterRw.Ops) (b : Slice U8) :
    LIB_ResultTotal.mapOuter (asOption entryV2)
      (do let reply ← NIJ_EntryModel.body b
          Result.ok (NCX_Install.mapReturn NCX_Carrier.entry reply)) =
    .ok (decodeEntryV2 (bytes b)) := by
  rw [←NIJ_EntryJoin.cohort base b]
  exact LIB_V2DecoderValues.entry_result b
/-- Every Option-valued field is a deterministic pure value at SAME bytes. -/
theorem registry1_returns (b : RSL.Bytes) (env : RSL.Env) :
    NND_Returned.Returns (RSL.Spec.pure (decodeRegistryV1 b)) env (decodeRegistryV1 b) :=
  NND_Returned.pure env _
theorem registry2_returns (b : RSL.Bytes) (env : RSL.Env) :
    NND_Returned.Returns (RSL.Spec.pure (decodeRegistryV2 b)) env (decodeRegistryV2 b) :=
  NND_Returned.pure env _
theorem entry1_returns (b : RSL.Bytes) (env : RSL.Env) :
    NND_Returned.Returns (RSL.Spec.pure (decodeEntryV1 b)) env (decodeEntryV1 b) :=
  NND_Returned.pure env _
theorem entry2_returns (b : RSL.Bytes) (env : RSL.Env) :
    NND_Returned.Returns (RSL.Spec.pure (decodeEntryV2 b)) env (decodeEntryV2 b) :=
  NND_Returned.pure env _
#print axioms policy_root
#print axioms registry1_model
#print axioms entry1_model
#print axioms registry1_root
#print axioms entry1_root
#print axioms registry2_root
#print axioms entry2_root
#print axioms registry1_returns
#print axioms registry2_returns
#print axioms entry1_returns
#print axioms entry2_returns
end LIB_PoolRegistry
