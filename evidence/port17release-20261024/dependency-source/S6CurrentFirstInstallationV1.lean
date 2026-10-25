import S6CurrentStage1CodecJoinV1
import S6CurrentVerifierCarrierV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisS6CurrentFirstInstallation
open AspisS6CurrentVerifierCarrier AspisS6CurrentCodecInstallation

def toDigest {H : Type} (digest : AdapterRw.aspis_core.digest.Digest32 H) :
    AspisR1CurrentCaller.aspis_core.digest.Digest32 H :=
  {coremarkerCopyInst:=digest.coremarkerCopyInst,digest:=digest.digest}

def toObserver (observer : Option (AdapterRw.aspis_r1_cost_probe.verifier.Phase → Result Unit)) :
    Option (AspisR1CurrentCaller.verifier.Phase → Result Unit) :=
  observer.map fun callback => fun phase => callback (fromPhase phase)

/-- Complete concrete tx1 child, with field-preserving public, unchanged digest
callback, all phases and errors, and the original returned checkpoint carrier. -/
def current (vops : AspisR1CurrentCaller.Ops) {H : Type}
    (digest : AdapterRw.aspis_core.digest.Digest32 H)
    (publicInput : AdapterRw.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (bytes proof : Slice U8) (split : Usize) (hash : H)
    (observer : Option (AdapterRw.aspis_r1_cost_probe.verifier.Phase → Result Unit)) :
    Result (core.result.Result (alloc.vec.Vec U8) AdapterRw.aspis_r1_cost_probe.verifier.Error) :=
  AspisS6OuterNativeOps.resultMap (AspisS6CurrentCodecInstallation.mapBoth id fromError)
    (AspisR1CurrentCaller.verifier.candidate.tx1 vops (toDigest digest)
      (toPublic publicInput) bytes proof split hash (toObserver observer))

def install (ops : AdapterRw.Ops) (vops : AspisR1CurrentCaller.Ops) : AdapterRw.Ops :=
  AspisS6CurrentCodecInstallation.install {ops with op10:=current vops}

theorem observer_none : toObserver none=none := rfl

theorem digest_call {H : Type} (digest : AdapterRw.aspis_core.digest.Digest32 H)
    (hash : H) (parts : Slice (Slice U8)) : (toDigest digest).digest hash parts=digest.digest hash parts := rfl

theorem selected_public (statement : AspisS6CurrentCodecInstallation.Statement) :
    (do let publicInput ← AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public statement
        ok (toPublic publicInput)) =
      ok (AspisR1CurrentCaller.FirstComposition.toCurrentPublic
        (AspisR1PublicPreparation.PreparationBinding.preparationPublic
          (AspisS6CurrentAdapterCarrier.toPoolV1PairForestTerminalStatementV1 statement))) := by
  cases statement <;> rfl

theorem current_success (vops : AspisR1CurrentCaller.Ops) {H : Type}
    (digest : AdapterRw.aspis_core.digest.Digest32 H)
    (publicInput : AdapterRw.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (bytes proof : Slice U8) (split : Usize) (hash : H) (checkpoint : alloc.vec.Vec U8)
    (accepted : current vops digest publicInput bytes proof split hash none=ok (.Ok checkpoint)) :
    AspisR1CurrentCaller.verifier.candidate.tx1 vops (toDigest digest)
      (toPublic publicInput) bytes proof split hash none=ok (.Ok checkpoint) := by
  unfold current at accepted
  cases run : AspisR1CurrentCaller.verifier.candidate.tx1 vops (toDigest digest)
      (toPublic publicInput) bytes proof split hash (toObserver none) with
  | fail e => simp only [run,AspisS6OuterNativeOps.resultMap] at accepted;cases accepted
  | div => simp only [run,AspisS6OuterNativeOps.resultMap] at accepted;cases accepted
  | ok reply =>
    cases reply with
    | Err e => simp only [run,AspisS6OuterNativeOps.resultMap,mapBoth] at accepted;cases accepted
    | Ok value => simp only [run,AspisS6OuterNativeOps.resultMap,mapBoth,id_eq] at accepted;cases accepted;exact run

private theorem map_bind {A B C : Type} (r : Result A) (f : A → B) (g : B → Result C) :
    (do let value ← AspisS6OuterNativeOps.resultMap f r;g value)=(do let value ← r;g (f value)) := by
  cases r <;> rfl

/-- Full Result equality of actual first_decoded with the concrete tx1 child.
Outer fail/div, Rust errors and the original error callback are retained. -/
theorem first_decoded_eq (ops : AdapterRw.Ops) (vops : AspisR1CurrentCaller.Ops)
    (publicInput : AdapterRw.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (bytes proof : Slice U8) (split : Usize) :
    AdapterRw.first_decoded (install ops vops) publicInput bytes proof split = (do
      let reply ← AspisR1CurrentCaller.verifier.candidate.tx1 vops
        (toDigest (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 (install ops vops)))
        (toPublic publicInput) bytes proof split () none
      AdapterRw.core.result.Result.map_err (BuiltinFnOnce AdapterRw.aspis_r1_cost_probe.verifier.Error AdapterRw.solana_program_error.ProgramError)
        (mapBoth id fromError reply) ops.op44) := by
  rw [AspisR1.AdapterRw.Cuts.first_decoded_call]
  change (do
    let reply ← current vops (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 (install ops vops)) publicInput bytes proof split () none
    AdapterRw.core.result.Result.map_err (BuiltinFnOnce AdapterRw.aspis_r1_cost_probe.verifier.Error AdapterRw.solana_program_error.ProgramError) reply ops.op44)=_
  unfold current
  rw [observer_none]
  exact map_bind _ _ _

#print axioms observer_none
#print axioms digest_call
#print axioms selected_public
#print axioms current_success
#print axioms first_decoded_eq
end AspisS6CurrentFirstInstallation
