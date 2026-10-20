import R9DeployedBinaryExperiment
import R16DecisionCheckpoint
import R20PoolStatementAgreement

/-! P2′ binds complete proof/public buffers, not just the physical checkpoint.
The R20 field-copy theorem is used at exactly its sameSnapshot boundary.
No claim of extracted Pool execution or of collision-free SHA is made. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.R9PoolRuntimeBinding
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

structure Inputs where
  proof : Bytes
  pub : Bytes

def digestMatches (hash : Bytes → State) (written current : Inputs) : Prop :=
  hash current.proof = hash written.proof ∧ hash current.pub = hash written.pub

/-- The exact same-buffer runtime premise supplied by P2′, scoped to one
writer/resume pair. It includes both full buffers, not a candidate prefix. -/
def P2Prime (hash : Bytes → State) (written current : Inputs) : Prop :=
  digestMatches hash written current →
    current.proof = written.proof ∧ current.pub = written.pub

theorem accepted_same_inputs (hash : Bytes → State) (written current : Inputs)
    (hP2 : P2Prime hash written current) (matched : digestMatches hash written current) :
    current = written := by
  obtain ⟨hp, hu⟩ := hP2 matched
  cases written
  cases current
  cases hp
  cases hu
  rfl

/-- Compiled counterexample: digest equality alone cannot replace P2′.
A constant digest accepts genuinely different complete public buffers. -/
theorem digest_equality_alone_false (state : State) :
    ∃ written current : Inputs,
      digestMatches (fun _ => state) written current ∧ current.pub ≠ written.pub := by
  refine ⟨⟨[], []⟩, ⟨[], [0]⟩, ⟨rfl, rfl⟩, ?_⟩
  intro h
  have hl := congrArg List.length h
  exact Nat.noConfusion hl

/-- The precise same-buffer law is false in the preceding collision model. -/
theorem no_p2_for_constant_digest (state : State) :
    ¬ P2Prime (fun _ => state) ⟨[], []⟩ ⟨[], [0]⟩ := by
  intro h
  have hl := congrArg List.length (h ⟨rfl, rfl⟩).2
  exact Nat.noConfusion hl

/-- P2′ transports any deterministic nested execution, with its complete
output/log type left unrestricted. -/
theorem nested_execution_same {O : Type} (execute : Inputs → O)
    (hash : Bytes → State) (written current : Inputs)
    (hP2 : P2Prime hash written current) (matched : digestMatches hash written current) :
    execute current = execute written :=
  congrArg execute (accepted_same_inputs hash written current hP2 matched)

/-- The ten/twelve matching checkpoint alone has no statement binding. This
is a counterexample to using that submodel as the complete Pool verifier,
not a counterexample to frozen Rust's two hash checks. -/
theorem unbound_matching_accepts_changed_public :
    ∃ (saved : R16DecisionCheckpoint.Checkpoint) (written current : Bytes),
      R16DecisionCheckpoint.tx2 saved = true ∧ current ≠ written := by
  refine ⟨R16DecisionCheckpoint.write R16DecisionCheckpoint.honestData
    R16DecisionCheckpoint.honestQueries, [], [0], ?_, ?_⟩
  · have ha := R16DecisionCheckpoint.honest_accepts
    have hs : R15WriterModel.Prefix R16DecisionCheckpoint.honestData
        R16DecisionCheckpoint.honestQueries 10 := fun _ _ => R16DecisionCheckpoint.honest_match _
    simpa only [R16DecisionCheckpoint.decision, R16DecisionCheckpoint.tx1,
      if_pos hs, R16DecisionCheckpoint.resume] using ha
  · intro h
    exact Nat.noConfusion (congrArg List.length h)

end AspisR1.R9PoolRuntimeBinding

namespace AspisR1AdapterReconstruct.R9PoolRuntimeBinding
open aspis_statement.pool_v1.pair_forest_terminal
open aspis_statement.pool_v1.pair_terminal
open aspis_statement.pool_v1.payment_relation
open r1_pool_adapter
open R20PoolStatementAgreement

/-- Both Pool variants use exactly R20's sameSnapshot field-copy result.
The payment payload and variant remain intact, including their different
wire discriminants. The deterministic serializer stays explicit. -/
theorem pool_common_from_r20 (accounts : AuthenticatedAsq8Accounts)
    (candidate : PoolV1PairVerifiedAfterstateV1) (snapshot : sameSnapshot accounts) :
    AdapterReconstructSuccess.common accounts candidate = poolCommon accounts candidate :=
  common_agreement accounts candidate snapshot

end AspisR1AdapterReconstruct.R9PoolRuntimeBinding

#print axioms AspisR1.R9PoolRuntimeBinding.accepted_same_inputs
#print axioms AspisR1.R9PoolRuntimeBinding.digest_equality_alone_false
#print axioms AspisR1.R9PoolRuntimeBinding.no_p2_for_constant_digest
#print axioms AspisR1.R9PoolRuntimeBinding.nested_execution_same
#print axioms AspisR1.R9PoolRuntimeBinding.unbound_matching_accepts_changed_public
#print axioms AspisR1AdapterReconstruct.R9PoolRuntimeBinding.pool_common_from_r20
end
