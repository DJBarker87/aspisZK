-- PCVF_ item 2 (parametric record AdapterRw.Ops, module AdapterRwModel). Statements: fresh = gate.
-- Fresh text: PCQD_E027 emission (prov-p1g-20261109/PCQD_E027_emitted/raw/PCQD_d01d, Aeneas b59d5188-extended, overflow ON),
-- declarations ProgramError/Pubkey/SolanaDigest instances, observer, first_decoded, OwnedAccount.data_len, require_verifier_checkpoint
-- (and the callee OwnedAccount.impl.owner). Their callees outside this list (core.result.Result.map_err, Result clone, Try.branch, ...)
-- resolve to the gate's definitions (retained assumption: core library models as in the gate; the emission has them as axioms).
-- The emission's seven cross-crate/SDK externals (axioms there) are the fields of `Ext` (a parameter, not declared as axioms).
-- RESULT CLASS: CONDITIONAL_ON_BINDING. The gate functions take `ops : Ops`; each equality below holds for every `ops` whose
-- used fields are bound to the corresponding external (hypotheses h*). Non-vacuity: `bound_exists` builds an Ops satisfying all of them.
import Aeneas
import AdapterRwModel
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace AdapterRw
namespace PRVFresh_ARM_k1

structure Ext where
  Hash : Type
  tx1 : ∀ {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H),
    aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public → (Slice Std.U8) → (Slice Std.U8) → Std.Usize → H →
    (Option (aspis_r1_cost_probe.verifier.Phase → Result Unit)) →
    Result (core.result.Result (alloc.vec.Vec Std.U8) aspis_r1_cost_probe.verifier.Error)
  checkpoint_size : aspis_r1_cost_probe.transport.Variant → Result Std.Usize
  to_bytes : Hash → Result (Array Std.U8 32#usize)
  perr_clone : solana_program_error.ProgramError → Result solana_program_error.ProgramError
  pk_eq : solana_pubkey.Pubkey → solana_pubkey.Pubkey → Result Bool
  hashv : (Slice (Slice Std.U8)) → Result Hash
  error : aspis_r1_cost_probe.verifier.Error → Result solana_program_error.ProgramError

@[reducible]
def solana_program_error.ProgramError.Insts.CoreCloneClone (x : Ext) : core.clone.Clone
  solana_program_error.ProgramError := {
  clone := x.perr_clone
}

@[reducible]
impl_def solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey (x : Ext) : core.cmp.PartialEq
  solana_pubkey.Pubkey solana_pubkey.Pubkey := {
  eq := x.pk_eq
  ne := core.cmp.PartialEq.ne.trait_default
    (solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey x)
}

def SolanaDigest.Insts.CoreCloneClone.clone
  (self : SolanaDigest) : Result SolanaDigest := do
  ok self

@[reducible]
def SolanaDigest.Insts.CoreCloneClone : core.clone.Clone SolanaDigest := {
  clone := SolanaDigest.Insts.CoreCloneClone.clone
}

@[reducible]
def SolanaDigest.Insts.CoreMarkerCopy : core.marker.Copy SolanaDigest := {
  cloneInst := SolanaDigest.Insts.CoreCloneClone
}

def SolanaDigest.Insts.Aspis_coreDigestDigest32.digest (x : Ext)
  (self : SolanaDigest) (parts : Slice (Slice Std.U8)) :
  Result (Array Std.U8 32#usize)
  := do
  let h ← x.hashv parts
  x.to_bytes h

@[reducible]
def SolanaDigest.Insts.Aspis_coreDigestDigest32 (x : Ext) : aspis_core.digest.Digest32
  SolanaDigest := {
  coremarkerCopyInst := SolanaDigest.Insts.CoreMarkerCopy
  digest := SolanaDigest.Insts.Aspis_coreDigestDigest32.digest x
}

def observer
  : Result (Option (aspis_r1_cost_probe.verifier.Phase → Result Unit)) := do
  ok none

def first_decoded (x : Ext)
  (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
  (public_bytes : Slice Std.U8) (proof : Slice Std.U8) (k : Std.Usize) :
  Result (core.result.Result (alloc.vec.Vec Std.U8)
    solana_program_error.ProgramError)
  := do
  let o ← observer
  let r ←
    x.tx1
      (SolanaDigest.Insts.Aspis_coreDigestDigest32 x) public1 public_bytes proof k
      () o
  core.result.Result.map_err (BuiltinFnOnce aspis_r1_cost_probe.verifier.Error
    solana_program_error.ProgramError) r (x.error)

def r1_pool_adapter.owned.OwnedAccount.impl.owner
  (self : r1_pool_adapter.owned.OwnedAccount) :
  Result solana_pubkey.Pubkey
  := do
  ok self.owner

def r1_pool_adapter.owned.OwnedAccount.data_len (x : Ext)
  (self : r1_pool_adapter.owned.OwnedAccount) :
  Result (core.result.Result Std.Usize solana_program_error.ProgramError)
  := do
  core.result.Result.Insts.CoreCloneClone.clone core.clone.CloneUsize
    (solana_program_error.ProgramError.Insts.CoreCloneClone x) self.length

def r1_pool_adapter.owned.require_verifier_checkpoint (x : Ext)
  (account : r1_pool_adapter.owned.OwnedAccount)
  (program_id : solana_pubkey.Pubkey) (writable : Bool) :
  Result (core.result.Result Unit solana_program_error.ProgramError)
  := do
  let p ← r1_pool_adapter.owned.OwnedAccount.impl.owner account
  let b ←
    core.cmp.impls.PartialEqShared.ne
      (solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey x) p program_id
  if b
  then
    ok (core.result.Result.Err
      solana_program_error.ProgramError.InvalidAccountData)
  else
    if account.is_signer
    then
      ok (core.result.Result.Err
        solana_program_error.ProgramError.InvalidAccountData)
    else
      if account.executable
      then
        ok (core.result.Result.Err
          solana_program_error.ProgramError.InvalidAccountData)
      else
        if account.is_writable != writable
        then
          ok (core.result.Result.Err
            solana_program_error.ProgramError.InvalidAccountData)
        else
          let r ← r1_pool_adapter.owned.OwnedAccount.data_len x account
          let cf ← core.result.Result.Insts.CoreOpsTry.branch r
          match cf with
          | core.ops.control_flow.ControlFlow.Continue val =>
            let i ←
              x.checkpoint_size
                aspis_r1_cost_probe.transport.Variant.S2
            if val != i
            then
              ok (core.result.Result.Err
                solana_program_error.ProgramError.InvalidAccountData)
            else ok (core.result.Result.Ok ())
          | core.ops.control_flow.ControlFlow.Break residual =>
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              Unit (core.convert.FromSame solana_program_error.ProgramError)
              residual

/-- The binding of the gate record's used fields to the emission's externals / fresh definitions. -/
structure Bound (ops : Ops) (x : Ext) : Prop where
  h10 : ∀ (H : Type) (i : aspis_core.digest.Digest32 H), @ops.op10 H i = @x.tx1 H i
  h12 : ops.op12 = x.checkpoint_size
  h35 : ops.op35 = x.perr_clone
  h36 : ops.op36 = x.pk_eq
  h42 : ops.op42 = SolanaDigest.Insts.CoreCloneClone.clone
  h43 : ops.op43 = SolanaDigest.Insts.Aspis_coreDigestDigest32.digest x
  h44 : ops.op44 = x.error

end PRVFresh_ARM_k1
end AdapterRw

namespace PRVEq.AdapterRwModel_k1
open AdapterRw AdapterRw.PRVFresh_ARM_k1

variable {ops : Ops} {x : Ext} (b : Bound ops x)
include b

theorem ProgramError_clone_inst :
    PRVFresh_ARM_k1.solana_program_error.ProgramError.Insts.CoreCloneClone x =
    AdapterRw.solana_program_error.ProgramError.Insts.CoreCloneClone ops := by
  unfold PRVFresh_ARM_k1.solana_program_error.ProgramError.Insts.CoreCloneClone AdapterRw.solana_program_error.ProgramError.Insts.CoreCloneClone
  rw [b.h35]

theorem SolanaDigest_clone_inst :
    PRVFresh_ARM_k1.SolanaDigest.Insts.CoreCloneClone = AdapterRw.SolanaDigest.Insts.CoreCloneClone ops := by
  unfold PRVFresh_ARM_k1.SolanaDigest.Insts.CoreCloneClone AdapterRw.SolanaDigest.Insts.CoreCloneClone
  rw [b.h42]

theorem SolanaDigest_copy_inst :
    PRVFresh_ARM_k1.SolanaDigest.Insts.CoreMarkerCopy = AdapterRw.SolanaDigest.Insts.CoreMarkerCopy ops := by
  unfold PRVFresh_ARM_k1.SolanaDigest.Insts.CoreMarkerCopy AdapterRw.SolanaDigest.Insts.CoreMarkerCopy
  rw [SolanaDigest_clone_inst b]

theorem SolanaDigest_digest32_inst :
    PRVFresh_ARM_k1.SolanaDigest.Insts.Aspis_coreDigestDigest32 x = AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 ops := by
  unfold PRVFresh_ARM_k1.SolanaDigest.Insts.Aspis_coreDigestDigest32 AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32
  rw [SolanaDigest_copy_inst b, b.h43]

theorem Pubkey_eq_inst :
    PRVFresh_ARM_k1.solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey x = AdapterRw.solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey ops := by
  unfold PRVFresh_ARM_k1.solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey AdapterRw.solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey
  rw [b.h36]

theorem observer_eq : PRVFresh_ARM_k1.observer = AdapterRw.observer ops := rfl

theorem first_decoded_eq :
    PRVFresh_ARM_k1.first_decoded x = AdapterRw.first_decoded ops := by
  funext p pb pr k
  unfold PRVFresh_ARM_k1.first_decoded AdapterRw.first_decoded
  rw [SolanaDigest_digest32_inst b, b.h10, b.h44]
  rfl

theorem data_len_eq :
    PRVFresh_ARM_k1.r1_pool_adapter.owned.OwnedAccount.data_len x = AdapterRw.r1_pool_adapter.owned.OwnedAccount.data_len ops := by
  funext self
  unfold PRVFresh_ARM_k1.r1_pool_adapter.owned.OwnedAccount.data_len AdapterRw.r1_pool_adapter.owned.OwnedAccount.data_len
  rw [ProgramError_clone_inst b]

theorem owner_eq :
    PRVFresh_ARM_k1.r1_pool_adapter.owned.OwnedAccount.impl.owner = AdapterRw.r1_pool_adapter.owned.OwnedAccount.impl.owner := rfl

theorem require_verifier_checkpoint_eq :
    PRVFresh_ARM_k1.r1_pool_adapter.owned.require_verifier_checkpoint x = AdapterRw.r1_pool_adapter.owned.require_verifier_checkpoint ops := by
  funext account program_id writable
  unfold PRVFresh_ARM_k1.r1_pool_adapter.owned.require_verifier_checkpoint AdapterRw.r1_pool_adapter.owned.require_verifier_checkpoint
  rw [owner_eq, data_len_eq b, b.h12, Pubkey_eq_inst b]
  done

end PRVEq.AdapterRwModel_k1
