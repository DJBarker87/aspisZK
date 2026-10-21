import OraclePortCheckpoint
import R9PoolConcreteExperiment

/-! Same-byte logical Pool instance for an oracle terminal. The finite-support
codec and ghost checkpoint remain the old logical model, not the frozen ABI. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortPool
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.CausalFirstHitUnionBound AspisV8R19.OracleResampling
open RawCutProverCompiler (Prover RunView)
open RawCutTranscriptRun (ErasedPrefix ErasedMessage)
open OraclePortExperiment (Decision recorded)
open R9TwoTransactionExperiment (Run)
open R9DeployedBinaryExperiment (Tx1 PoolTx2 deployed deployedFailureModel mass failure)
open R9PoolSavedTenModel (Checkpoint prepare write stage1 stage1_eval)
open R9PoolConcreteExperiment (PoolChecks Policy Tape admitted postcheck postcheck_acceptance rejectRun)
open OraclePortCheckpoint (resume resume_recorded)
attribute [local instance] Classical.propDecidable
abbrev tx1 := R9PoolConcreteExperiment.tx1

def CallerReachability (tx1 : Tx1) (poolTx2 : PoolTx2)
    (D : LiteralByteProtocol.Decoder) (dO : Decision) (P : Prover) : Prop :=
  ∀ H run, (eval H (deployed tx1 poolTx2)).2.resumed = some run →
    run.2.2 = true → run = eval H (recorded D dO P)

def checkedResume (D : LiteralByteProtocol.Decoder)
    (d : Decision) (checks : PoolChecks)
    (c : Checkpoint) : Program Bytes State Run :=
  bind (resume D d c) fun run => .done (postcheck checks run)

/-- The runtime model's persisted bytes are supplied as the function argument.
Same-byte checkpoint handoff therefore introduces no additional interpreter reset. -/
def poolTx2 (D : LiteralByteProtocol.Decoder)
    (d : Decision) (P : Prover) (policy : Policy) : PoolTx2 :=
  fun bytes => match R9PoolCheckpointCodec.decode (stage1 D P) bytes with
  | some (some c) => if admitted (policy c) then checkedResume D d (policy c) c else .done rejectRun
  | _ => .done rejectRun

theorem caller (D : LiteralByteProtocol.Decoder)
    (d : Decision) (P : Prover)
    (tape : Tape) (policy : Policy) :
    CallerReachability (tx1 D P tape) (poolTx2 D d P policy) D d P := by
  intro H run hr ha
  have he : (eval H (tx1 D P tape)).2 =
      ⟨(eval H (stage1 D P)).2.map
        (fun c => R9PoolCheckpointCodec.encode (stage1 D P) (some c)),
       match (eval H (stage1 D P)).2 with | none => fun _ => 0 | some c => tape c.raw⟩ := by
    simp only [tx1, R9PoolConcreteExperiment.tx1, eval_bind, eval]
    rfl
  cases hs : (eval H (stage1 D P)).2 with
  | none =>
    simp only [deployed, R9TwoTransactionExperiment.experiment, eval_bind, he, hs,
      Option.map_none, eval] at hr
    contradiction
  | some c =>
    have hdecode := R9PoolCheckpointCodec.persisted_output (stage1 D P) H
    rw [hs] at hdecode
    have hfirst : (eval H (tx1 D P tape)).2.checkpoint =
        some (R9PoolCheckpointCodec.encode (stage1 D P) (some c)) := by
      rw [he, hs]; rfl
    have hexp := R9TwoTransactionExperiment.eval_success (tx1 D P tape)
      (poolTx2 D d P policy) H _ hfirst
    change (eval H (R9TwoTransactionExperiment.experiment _ _)).2.resumed = some run at hr
    rw [hexp] at hr
    have hp : (eval H (poolTx2 D d P policy
        (R9PoolCheckpointCodec.encode (stage1 D P) (some c)))).2 = run :=
      Option.some.inj hr
    unfold poolTx2 at hp
    rw [hdecode] at hp
    change (eval H (if admitted (policy c) then checkedResume D d (policy c) c
      else .done rejectRun)).2 = run at hp
    by_cases hg : admitted (policy c) = true
    · rw [if_pos hg] at hp
      simp only [checkedResume, eval_bind, eval] at hp
      have hpost := postcheck_acceptance (policy c) (eval H (resume D d c)).2
        (by rw [hp]; exact ha)
      have hresume : (eval H (resume D d c)).2 = run := hpost.2.symm.trans hp
      have hw : write (eval H (prepare D P)) = some c := by
        rw [← stage1_eval D P H]; exact hs
      rw [← hresume]
      exact resume_recorded D d P H c hw hpost.1
    · rw [if_neg hg] at hp
      have hf : run.2.2 = false := by rw [← hp]; rfl
      rw [hf] at ha
      contradiction

/-- The caller identity gives the same shared-oracle failure transport.
Only one query-scan allowance is retained; it is not a second scan. -/
theorem transport (tx1 : Tx1) (poolTx2 : PoolTx2)
    (D : LiteralByteProtocol.Decoder) (dO : Decision) (P : Prover)
    (hc : CallerReachability tx1 poolTx2 D dO P) :
    deployedFailureModel tx1 poolTx2 ≤ lazyMean (recorded D dO P) emptyTable
      RawRecordedOracleExtractionMassBin.failureMass +
      QueryScanModelFailure.failureProbability (2^18) := by
  have hle : deployedFailureModel tx1 poolTx2 ≤
      lazyMean (recorded D dO P) emptyTable RawRecordedOracleExtractionMassBin.failureMass := by
    apply OracleProgramLawExt.lazyMean_le_of_eval
    intro H
    apply mean_mono
    intro coins
    apply indicator_mono
    rintro ⟨run, hr, ha, hf⟩
    have he := hc H run hr ha
    exact ⟨by simpa only [← he] using ha, by simpa only [← he] using hf⟩
  have hn : 0 ≤ QueryScanModelFailure.failureProbability (2^18) := by
    unfold QueryScanModelFailure.failureProbability
    positivity
  exact hle.trans (le_add_of_nonneg_right hn)

theorem deployed_transport (D : LiteralByteProtocol.Decoder) (dO : Decision) (P : Prover)
    (tape : Tape) (policy : Policy) :
    deployedFailureModel (tx1 D P tape) (poolTx2 D dO P policy) ≤
      lazyMean (recorded D dO P) emptyTable RawRecordedOracleExtractionMassBin.failureMass +
      QueryScanModelFailure.failureProbability (2^18) :=
  transport _ _ D dO P (caller D dO P tape policy)

/-- The remaining source join is equality of the designated resumed observation with
this constructed control-flow model, including its designated recorded log. Physical checkpoint encodings and
outer runtime-only calls are deliberately not compared.
It is not a probability hypothesis and is not proved by P2′ alone. -/
def RustPoolEqualsModel (rustTx1 : Tx1) (rustPoolTx2 : PoolTx2)
    (D : LiteralByteProtocol.Decoder) (d : Decision)
    (P : Prover) (tape : Tape) (policy : Policy) : Prop :=
  ∀ H, (eval H (deployed rustTx1 rustPoolTx2)).2.resumed =
    (eval H (deployed (tx1 D P tape) (poolTx2 D d P policy))).2.resumed

theorem source_caller (rustTx1 : Tx1) (rustPoolTx2 : PoolTx2)
    (D : LiteralByteProtocol.Decoder) (d : Decision)
    (P : Prover) (tape : Tape) (policy : Policy)
    (join : RustPoolEqualsModel rustTx1 rustPoolTx2 D d P tape policy) :
    CallerReachability rustTx1 rustPoolTx2 D d P := by
  intro H run hr ha
  exact caller D d P tape policy H run (by rw [join H] at hr; exact hr) ha

#print axioms caller
#print axioms transport
#print axioms deployed_transport
#print axioms source_caller
end AspisR1.OraclePortPool
end
