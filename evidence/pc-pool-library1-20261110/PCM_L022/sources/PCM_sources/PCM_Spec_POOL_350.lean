import PCM_Carriers
set_option autoImplicit false
namespace PCM_POOL_350
open RSL PCM PCM.Computation
structure Args where
  pool_program : B32
  master : AccountInfo
  checkpoint : AccountInfo
  lane : AccountInfo
  policy : VerifierPolicy
  registry : List AccountInfo
  verifier_program : AccountInfo
  proof : AccountInfo
  verifier_checkpoint : Option AccountInfo
  request : Request
  current_slot : UInt64
  request_bytes : Bytes
structure Selection where
  verifier_program : B32
  profile_binding : B32
  release_binding : B32
  statement_version : UInt8
structure Authenticated where
  policy : VerifierPolicy
  pool : B32
  verifier_program : B32
  profile_binding : B32
  release_binding : B32
  statement_version : UInt8
  registry_generation : UInt64
  expected_verifier_loader : Option B32
  authenticated_at_slot : UInt64
structure Children where
  proofTransport : Child (AccountInfo × AccountInfo × Option AccountInfo) B32
  requireProgram : Child (AccountInfo × B32) Unit
  distinctCheckpoint : Child (Option AccountInfo × AccountInfo × AccountInfo × AccountInfo × List AccountInfo) Unit
  authenticate : Child (B32 × VerifierPolicy × List AccountInfo × Selection × UInt64) Authenticated
  matchesOwner : Authenticated → B32 → Bool
  matches : Authenticated → B32 → B32 → B32 → B32 → UInt8 → Bool

def duplicateKeys : List B32 → Bool
  | [] => false
  | k::ks => ks.any (fun x => decide (x=k)) || duplicateKeys ks

def Ref (C : Children) (a : Args) : Computation DispatchPlan := do
  check (decide (a.request.pool_program ≠ a.pool_program)) (.custom 0x4153202b)
  let selected ← C.proofTransport.call (a.verifier_program,a.proof,a.verifier_checkpoint)
  C.requireProgram.call (a.verifier_program,selected)
  C.distinctCheckpoint.call (a.verifier_checkpoint,a.master,a.checkpoint,a.lane,a.registry)
  let auth ← C.authenticate.call (a.master.key,a.policy,a.registry,
    ⟨selected,a.request.verifier_profile,a.request.verifier_release,TERMINAL_VERSION⟩,a.current_slot)
  check (!C.matchesOwner auth a.verifier_program.owner) (.custom 0x41532027)
  check (!C.matches auth a.master.key selected a.request.verifier_profile a.request.verifier_release TERMINAL_VERSION) (.custom 0x41532012)
  check (duplicateKeys [a.proof.key,a.master.key,a.checkpoint.key,a.lane.key]) .invalidArgument
  check (decide (a.master.owner ≠ a.pool_program) || a.master.executable || a.master.is_signer ||
    decide (a.checkpoint.owner ≠ a.pool_program) || a.checkpoint.executable || a.checkpoint.is_signer ||
    decide (a.lane.owner ≠ a.pool_program) || a.lane.executable || a.lane.is_signer) .invalidAccountData
  Computation.pure ⟨selected,a.request_bytes⟩
def RowSpec (C : Children) (impl : Args → State → Env → Observation DispatchPlan) : Prop :=
  PCM.RowSpec (fun _ => True) (Ref C) impl
end PCM_POOL_350
