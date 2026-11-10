-- PCWT_ binding discharge for six AdapterRwModel keys: observer, SolanaDigest Clone / Copy / Digest32 instances, ProgramError Clone instance, OwnedAccount.data_len. Route (b).
-- What was bound (PCVF_ k1): the fresh text (PCQD_E027, frozen 4bb3b3f, ON) has seven externals as fields of Ext; the gate record AdapterRw.Ops carries them as slots op10, op12, op35, op36, op42, op43, op44.
-- The six keys here use only: op42 (SolanaDigest::clone, Aspis derive, fresh text `ok self`: bound to the fresh frozen definition by construction of ops0),
-- op43 (SolanaDigest::digest := the fresh frozen body over Hash::hashv / to_bytes: SDK items, HM-A, parameters of Sdk), op35 (ProgramError::clone: SDK, HM-A, parameter of Sdk).
-- ops0 and x0 are constructed from Sdk; the slots these keys do not use (op10 tx1, op12 checkpoint_size, op36 Pubkey eq, op44 error) are panic on both sides and are NOT claimed bound.
-- Statement: fresh (x0 s) = gate (ops0 s) for every SDK parameter s.  The deployed AdapterRw Ops (DrvI_Installation.sdk) is not related here.
import Aeneas
import AdapterRwModel
import PRVEq_AdapterRwModel_k1
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
noncomputable section

namespace PRVEq.AdapterRwModel_t6
open AdapterRw AdapterRw.PRVFresh_ARM_k1

/-- the SDK items (HM-A) used by the six keys -/
structure Sdk where
  Hash : Type
  to_bytes : Hash → Result (Array Std.U8 32#usize)
  perr_clone : solana_program_error.ProgramError → Result solana_program_error.ProgramError
  hashv : (Slice (Slice Std.U8)) → Result Hash

def x0 (s : Sdk) : Ext where
  Hash := s.Hash
  tx1 := fun _ _ _ _ _ _ _ => fail .panic
  checkpoint_size := fun _ => fail .panic
  to_bytes := s.to_bytes
  perr_clone := s.perr_clone
  pk_eq := fun _ _ => fail .panic
  hashv := s.hashv
  error := fun _ => fail .panic

def ops0 (s : Sdk) : Ops :=
  { PRVEq.AdapterRwModel_k1.panicOps with
      op10 := fun {H} i => (x0 s).tx1 i
      op12 := (x0 s).checkpoint_size
      op35 := (x0 s).perr_clone
      op36 := (x0 s).pk_eq
      op42 := SolanaDigest.Insts.CoreCloneClone.clone
      op43 := SolanaDigest.Insts.Aspis_coreDigestDigest32.digest (x0 s)
      op44 := (x0 s).error }

theorem bound (s : Sdk) : PRVFresh_ARM_k1.Bound (ops0 s) (x0 s) := by
  exact ⟨fun H i => rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem observer_frozen (s : Sdk) : PRVFresh_ARM_k1.observer = AdapterRw.observer (ops0 s) :=
  PRVEq.AdapterRwModel_k1.observer_eq (bound s)

theorem SolanaDigest_clone_frozen (s : Sdk) :
    PRVFresh_ARM_k1.SolanaDigest.Insts.CoreCloneClone = AdapterRw.SolanaDigest.Insts.CoreCloneClone (ops0 s) :=
  PRVEq.AdapterRwModel_k1.SolanaDigest_clone_inst (bound s)

theorem SolanaDigest_copy_frozen (s : Sdk) :
    PRVFresh_ARM_k1.SolanaDigest.Insts.CoreMarkerCopy = AdapterRw.SolanaDigest.Insts.CoreMarkerCopy (ops0 s) :=
  PRVEq.AdapterRwModel_k1.SolanaDigest_copy_inst (bound s)

theorem SolanaDigest_digest32_frozen (s : Sdk) :
    PRVFresh_ARM_k1.SolanaDigest.Insts.Aspis_coreDigestDigest32 (x0 s) =
    AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 (ops0 s) :=
  PRVEq.AdapterRwModel_k1.SolanaDigest_digest32_inst (bound s)

theorem ProgramError_clone_frozen (s : Sdk) :
    PRVFresh_ARM_k1.solana_program_error.ProgramError.Insts.CoreCloneClone (x0 s) =
    AdapterRw.solana_program_error.ProgramError.Insts.CoreCloneClone (ops0 s) :=
  PRVEq.AdapterRwModel_k1.ProgramError_clone_inst (bound s)

theorem data_len_frozen (s : Sdk) :
    PRVFresh_ARM_k1.r1_pool_adapter.owned.OwnedAccount.data_len (x0 s) =
    AdapterRw.r1_pool_adapter.owned.OwnedAccount.data_len (ops0 s) :=
  PRVEq.AdapterRwModel_k1.data_len_eq (bound s)

end PRVEq.AdapterRwModel_t6
#print axioms PRVEq.AdapterRwModel_t6.observer_frozen
#print axioms PRVEq.AdapterRwModel_t6.SolanaDigest_clone_frozen
#print axioms PRVEq.AdapterRwModel_t6.SolanaDigest_copy_frozen
#print axioms PRVEq.AdapterRwModel_t6.SolanaDigest_digest32_frozen
#print axioms PRVEq.AdapterRwModel_t6.ProgramError_clone_frozen
#print axioms PRVEq.AdapterRwModel_t6.data_len_frozen
