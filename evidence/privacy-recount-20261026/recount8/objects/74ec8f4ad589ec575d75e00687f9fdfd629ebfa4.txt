import R1Z.PV_RunJoin_LedgerWorld
import R1Z.PV_RunJoin_ReservationGuards
import R1Z.PV_RunJoin_GenericSourceCaller
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PublicReservation
open Aeneas Aeneas.Std Result ProverRwFull ProverRwRetryModel
variable [ExternalTypes] [ExternalFuns]

def guards (address : PV_RunJoin_LedgerWorld.Address)
    (nonce : Array U8 32#usize)
    (context : aspis_core.state_only_hiding.StateOnlyHidingContext) :
    Result (Option ProverCommitLedger36.Path) := do
  let different ← core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8 context.mask_nonce nonce
  if different then .ok none else
    let mask ← aspis_core.state_only_hiding.PINNED_POOL_V1_PAIR_FOREST_RELATION_FREE_MASK_FINGERPRINT_V1
    if context.mask_layout_fingerprint != mask then .ok none else
      let factor ← aspis_core.state_only_hiding.PINNED_POOL_V1_PAIR_FOREST_HIDING_LAYOUT_FACTOR_FINGERPRINT_V1
      if context.layout_factor_fingerprint != factor then .ok none else
        .ok (some (address context.mask_nonce))

/-- ONE public reservation decision, before the compiler-dependent body.
It preserves every extracted prefix call and its machine failure/divergence.
The context/nonce check is the actual source guard, not an assumed success. -/
def entry (address : PV_RunJoin_LedgerWorld.Address) (pub : Pub)
    (variant : transport.Variant) (hash : Hash) (nonce : Array U8 32#usize) :
    Result (Option ProverCommitLedger36.Path) := do
  let r ← aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes pub
  let r1 ← core.result.Result.map_err
    prover.prove_masked_attempt.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError r ()
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
  match cf with
  | .Continue val =>
    let (context,_) ← ProverRwOuterPrefix.prepare val variant hash nonce
    guards address nonce context
  | .Break residual =>
    let _ ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      Proof (core.convert.FromSame verifier.Error) residual
    .ok none

/-- Neither compiled witness columns nor private field-mask entropy are
arguments to the public reservation function. Equal public inputs and nonce
therefore give literal equality, including prefix errors and divergence. -/
theorem common (address : PV_RunJoin_LedgerWorld.Address)
    (pub pub' : Pub) (variant : transport.Variant) (hash hash' : Hash)
    (nonce nonce' : Array U8 32#usize)
    (public_eq : pub = pub') (hash_eq : hash = hash') (nonce_eq : nonce = nonce') :
    entry address pub variant hash nonce = entry address pub' variant hash' nonce' := by
  rw [public_eq,hash_eq,nonce_eq]

#print axioms common
end R1Z.PV_RunJoin_PublicReservation
