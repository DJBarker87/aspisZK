-- PCVF_ item 4 (two of the 23 not-attempted records), second shape: fresh text with the emission's external axioms replaced by
-- parameters, gate = the NMT gate form that already takes its opaque callees as explicit parameters (NMT_call_k).
-- Fresh text: NMT_first -> prov-p2d-20261109/inputs/fresh_NMT_first_Funs/Funs.lean (Aeneas emission of programs/r1-cost-probe/src/lib.rs, SolanaDigest);
-- NMT_stage1_owned -> evidence/model-bridge-20261111/NND_reuse/NMT_fresh/NMT_extracted/stage1_owned/raw/NMT_stage1_owned/Funs.lean (OwnedAccount.data).
-- Statements are universally quantified over the external callees (the gate's NMT_call_k); which concrete frozen items they are is
-- the binding made where the gate is instantiated (CONDITIONAL_ON_BINDING); the callee order is read off the bodies.
-- Types are read as the gate's declarations of the same name (same declaration text in the emission's Types.lean).
import Aeneas
import NMT_first.Funs
import NMT_stage1_owned.Funs
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace NMT_first
namespace PRVFresh_k1

def SolanaDigest.Insts.Aspis_coreDigestDigest32.digest
  (to_bytes : solana_hash.Hash → Result (Array Std.U8 32#usize))
  (hashv : (Slice (Slice Std.U8)) → Result solana_hash.Hash)
  (self : SolanaDigest) (parts : Slice (Slice Std.U8)) :
  Result (Array Std.U8 32#usize)
  := do
  let h ← hashv parts
  to_bytes h

@[reducible]
def SolanaDigest.Insts.Aspis_coreDigestDigest32
  (to_bytes : solana_hash.Hash → Result (Array Std.U8 32#usize))
  (hashv : (Slice (Slice Std.U8)) → Result solana_hash.Hash) : aspis_core.digest.Digest32
  SolanaDigest := {
  coremarkerCopyInst := SolanaDigest.Insts.CoreMarkerCopy
  digest := SolanaDigest.Insts.Aspis_coreDigestDigest32.digest to_bytes hashv
}

end PRVFresh_k1
end NMT_first

namespace NMT_stage1_owned
namespace PRVFresh_k1

def r1_pool_adapter.owned.OwnedAccount.data
  (clone : solana_program_error.ProgramError → Result solana_program_error.ProgramError)
  (self : r1_pool_adapter.owned.OwnedAccount) :
  Result (core.result.Result (Slice Std.U8) solana_program_error.ProgramError)
  := do
  match self.bytes with
  | core.result.Result.Ok bytes =>
    let s := alloc.vec.Vec.deref bytes
    ok (core.result.Result.Ok s)
  | core.result.Result.Err error =>
    let pe ← clone error
    ok (core.result.Result.Err pe)

end PRVFresh_k1
end NMT_stage1_owned

theorem PRVEq.NMT_first.digest_k1 :
    @NMT_first.PRVFresh_k1.SolanaDigest.Insts.Aspis_coreDigestDigest32.digest =
    @NMT_first.SolanaDigest.Insts.Aspis_coreDigestDigest32.digest := rfl

theorem PRVEq.NMT_first.digest_inst_k1 :
    @NMT_first.PRVFresh_k1.SolanaDigest.Insts.Aspis_coreDigestDigest32 =
    @NMT_first.SolanaDigest.Insts.Aspis_coreDigestDigest32 := rfl

theorem PRVEq.NMT_stage1_owned.data_k1 :
    @NMT_stage1_owned.PRVFresh_k1.r1_pool_adapter.owned.OwnedAccount.data =
    @NMT_stage1_owned.r1_pool_adapter.owned.OwnedAccount.data := rfl

#print axioms PRVEq.NMT_first.digest_k1
#print axioms PRVEq.NMT_first.digest_inst_k1
#print axioms PRVEq.NMT_stage1_owned.data_k1
