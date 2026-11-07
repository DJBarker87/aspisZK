import RSL_Pool
import PCM_PolicyValue
import PCM_V1DecoderValues
import PCM_V2DecoderValues
import NJY_Roots
import NHY_RegistryJoin
import NIS_EntryJoin
set_option autoImplicit false
noncomputable section
namespace PCM_Inst_Registry
open Aeneas Aeneas.Std NND_Carrier PCM_V1DecoderValues
abbrev validatePolicy := PCM_PolicyValue.validate
abbrev decodeRegistryV1 := PCM_V1DecoderValues.registry
abbrev decodeRegistryV2 := PCM_V2DecoderValues.registry
abbrev decodeEntryV1 := PCM_V1DecoderValues.entry
abbrev decodeEntryV2 := PCM_V2DecoderValues.entry
/-- CLOSED policy supplier, at the actual deployed slot and SAME policy. -/
theorem policy_root {E : Type} (missing : AspisR1.IDa_Deployed.Uninstalled E)
    (devnet : Bool) (indexError : E) (reservation : AspisR1.NP6_StdModel.Reservation)
    (p : NHY_PolicyModel.Policy) :
    PCM_ResultTotal.mapOuter PCM_PolicyValue.isOk
      ((NHJ_DeployedIds.configuration (NHY_PolicyModel.bindPolicy missing)
        devnet indexError reservation).adapter.op15 p) =
    .ok (validatePolicy (policy p)) := by
  rw [NHY_PolicyModel.actual_slot]
  exact PCM_PolicyValue.native p
/-- Deterministic graph of CLOSED TX2:203's model, never the image of Cut. -/
theorem registry1_model (b : Slice U8) :
    PCM_ResultTotal.mapOuter (asOption registryV1)
      (NJQ_Canonical.mapOuter NJQ_Canonical.registryResult (NJY_Registry.model b)) =
    .ok (decodeRegistryV1 (PCM_Bytes.bytes b)) := PCM_V1DecoderValues.registry_result b
theorem entry1_model (b : Slice U8) :
    PCM_ResultTotal.mapOuter (asOption entryV1)
      (NJQ_Canonical.mapOuter NJQ_Canonical.entryResult (NJY_Entry.model b)) =
    .ok (decodeEntryV1 (PCM_Bytes.bytes b)) := PCM_V1DecoderValues.entry_result b
/-- The supplied CLOSED root is composed at exactly b, log and out. -/
theorem registry1_root (b : Slice U8) (log : Option NJI_V1Carrier.R)
    (out : core.result.Result NJI_V1Carrier.R NJI_V1Carrier.F)
    (cut : NJY_Registry.Cut b log out) :
    asOption registryV1 (NJQ_Canonical.registryResult out) = decodeRegistryV1 (PCM_Bytes.bytes b) := by
  have h := registry1_model b
  rw [←NJY_Roots.registry b log out cut] at h
  exact Result.ok.inj h
theorem entry1_root (b : Slice U8) (log : Option NJI_V1Carrier.E)
    (out : core.result.Result NJI_V1Carrier.E NJI_V1Carrier.F)
    (cut : NJY_Entry.Cut b log out) :
    asOption entryV1 (NJQ_Canonical.entryResult out) = decodeEntryV1 (PCM_Bytes.bytes b) := by
  have h := entry1_model b
  rw [←NJY_Roots.entry b log out cut] at h
  exact Result.ok.inj h
/-- Bind the V2 graph directly to its CLOSED cohort model equation. -/
theorem registry2_root (base : AdapterRw.Ops) (b : Slice U8) :
    PCM_ResultTotal.mapOuter (asOption registryV2)
      (do let reply ← NHY_RegistryModel.body b
          Result.ok (NCX_Install.mapReturn NCX_Carrier.registry reply)) =
    .ok (decodeRegistryV2 (PCM_Bytes.bytes b)) := by
  rw [←NHY_RegistryJoin.cohort base b]
  exact PCM_V2DecoderValues.registry_result b
theorem entry2_root (base : AdapterRw.Ops) (b : Slice U8) :
    PCM_ResultTotal.mapOuter (asOption entryV2)
      (do let reply ← NIJ_EntryModel.body b
          Result.ok (NCX_Install.mapReturn NCX_Carrier.entry reply)) =
    .ok (decodeEntryV2 (PCM_Bytes.bytes b)) := by
  rw [←NIJ_EntryJoin.cohort base b]
  exact PCM_V2DecoderValues.entry_result b
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

/-- Five complete shared fields, fixed independently of the remaining library. -/
structure Fields where
  validatePolicy : RSL.VerifierPolicy → Bool
  decodeRegistryV1 : RSL.Bytes → Option RSL.RegistryV1
  decodeRegistryV2 : RSL.Bytes → Option RSL.RegistryV2
  decodeEntryV1 : RSL.Bytes → Option RSL.EntryV1
  decodeEntryV2 : RSL.Bytes → Option RSL.EntryV2

def fields : Fields := ⟨validatePolicy,decodeRegistryV1,decodeRegistryV2,decodeEntryV1,decodeEntryV2⟩

def install (remaining : RSL.PoolLib) : RSL.PoolLib :=
  { remaining with validatePolicy := fields.validatePolicy,
    decodeRegistryV1 := fields.decodeRegistryV1,decodeRegistryV2 := fields.decodeRegistryV2,
    decodeEntryV1 := fields.decodeEntryV1,decodeEntryV2 := fields.decodeEntryV2 }

/-- Literal model graph, never the image of a Cut/Windows relation. -/
def graph {A B : Type} (model : A → B) (a : A) : RSL.Spec B :=
  fun _ o => True ∧ o = ⟨.ret (model a),[]⟩

theorem graph_exact {A B : Type} (model : A → B) (a : A) (env : RSL.Env) (o : RSL.Obs B) :
    graph model a env o ↔ True ∧ o = ⟨.ret (model a),[]⟩ := Iff.rfl

theorem graph_functional {A B : Type} (model : A → B) (a : A) :
    RSL.Spec.Functional (graph model a) := by
  intro env
  exact ⟨⟨.ret (model a),[]⟩,fun _ => ⟨fun h => h.2,fun h => ⟨trivial,h⟩⟩⟩

def resultType {A B : Sort _} (_ : A → B) := B

theorem policy_type : resultType RSL.PoolLib.validatePolicy = (RSL.VerifierPolicy → Bool) := rfl
theorem registry1_type : resultType RSL.PoolLib.decodeRegistryV1 = (RSL.Bytes → Option RSL.RegistryV1) := rfl
theorem registry2_type : resultType RSL.PoolLib.decodeRegistryV2 = (RSL.Bytes → Option RSL.RegistryV2) := rfl
theorem entry1_type : resultType RSL.PoolLib.decodeEntryV1 = (RSL.Bytes → Option RSL.EntryV1) := rfl
theorem entry2_type : resultType RSL.PoolLib.decodeEntryV2 = (RSL.Bytes → Option RSL.EntryV2) := rfl

theorem installed_policy (remaining : RSL.PoolLib) : (install remaining).validatePolicy = validatePolicy := rfl
theorem installed_registry1 (remaining : RSL.PoolLib) : (install remaining).decodeRegistryV1 = decodeRegistryV1 := rfl
theorem installed_registry2 (remaining : RSL.PoolLib) : (install remaining).decodeRegistryV2 = decodeRegistryV2 := rfl
theorem installed_entry1 (remaining : RSL.PoolLib) : (install remaining).decodeEntryV1 = decodeEntryV1 := rfl
theorem installed_entry2 (remaining : RSL.PoolLib) : (install remaining).decodeEntryV2 = decodeEntryV2 := rfl
#print axioms graph_exact
#print axioms graph_functional
#print axioms policy_type
#print axioms registry1_type
#print axioms registry2_type
#print axioms entry1_type
#print axioms entry2_type
#print axioms installed_policy
#print axioms installed_registry1
#print axioms installed_registry2
#print axioms installed_entry1
#print axioms installed_entry2
end PCM_Inst_Registry
