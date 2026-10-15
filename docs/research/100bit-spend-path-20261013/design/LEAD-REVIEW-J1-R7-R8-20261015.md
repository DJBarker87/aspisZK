# Lead review of the J1.R7/R8 continuation (98c316524, 7c5ca8699)

Branch `codex/r1-j1-r7-r8-20261015` (base e4a5808dd). Not yet merged: both it
and the live branch (b400d586a, 5dba4e426) **create**
`lean/LiteralByteProtocol.lean` independently (add/add conflict, three hunks).
The session that owns it merges, keeps both sides' declarations under one
module, recompiles `R1LiteralByteProtocol` and every module importing it, and
pushes the merge to `codex/100bit-spend-path-20261013`. The lead does not
resolve Lean conflicts without a compile.

## J1.R10 Accepted

- **G_R1.7 guard.** `pool_route::admitted` (exact `[3,10]`, `[3,11]`,
  `ASQ8…`) is checked before any account access; legacy routing exists only
  under `cfg(not(feature="pool-adapter"))`; lifecycle 4/5/6 rejected; native
  tests pass. Accepted. Closure needs the SBF rebuild and artifact pin (J1.R13).
- **R7.** `AllAddressFiatShamir.soundness_bound` (arbitrary address type,
  memoised lazy oracle) and `LiteralByteProtocol.conditional_bound`
  (`Q·maxErr(ε,33) + κ(Q)` under D1, density, D3, ReadsChains, LazyInj and the
  first-read budget) are accepted as conditional theorems. The refusal to
  transport injectivity through the non-injective `Addr.toBytes` is correct.
  Open and owed: the raw-byte collision mass `κ(Q) ≤ 12·Q²/2^256`.
- **J1.a/J1.b adapters** (`PublicSourceRaw*`, `PublicSourceBoundary`,
  `LiteralSemantic{Codec,Payload}Bridge`) accepted as models with
  `SourceSerializerRefines` as an explicit hypothesis. A handwritten model is
  not the Rust; the extraction stays item 1 of the queue.
- **QV inventory** (stage1 118+21k, stage2 core 465, PDA searches) accepted as
  an inventory only; superseded in part by J1.R12.

## J1.R11 Decision: provisioning without lifecycle routes

The lifecycle routes stay rejected. The trusted precondition "proof bytes
immutable after finalisation" from decision 1 is **withdrawn** and replaced by
what the code already checks: `resume` (verifier.rs:325-328) recomputes
`hash(proof)` and `hash(public)` and compares them with the values tx1 wrote
into the checkpoint. A change to either buffer between tx1 and tx2 is a
rejection, except on a hash collision already charged in κ(Q). Therefore:

1. **Proof and public buffers** may have any owner. stage1/stage2 read them
   read-only and do not require `owner == program_id` or a lifecycle header.
   Uploading uses an ordinary buffer the uploader controls (any program, e.g.
   a minimal upload program or a system-owned account written by the payer).
2. **Checkpoint account**: owned by the verifier program, created zeroed by
   the system program with `owner = program_id` (anyone can do this), and
   stage1 writes only into an all-zero account of exactly `checkpoint_size(v)`
   bytes (the legacy `[1,k]` rule). stage1 and stage2 are then the only
   writers of program-owned data, which is the remaining trusted precondition,
   now discharged by G_R1.7 plus this rule.
3. The proof-account and public-account checks at
   `r1_pool_adapter.rs:875-889` change accordingly (G_R1.9). The checkpoint
   must be a distinct account from both buffers. The statement binding to Pool
   state (ASF8 fields, anchor history, nullifier freshness) is unchanged and
   stays in the Pool adapter.
4. CU: the whole-proof hash is already in tx2's resume; no new cost except
   whatever the lifecycle header parse saved.

## J1.R12 Decision: PDA searches and runtime pin

1. Replace `find_program_address` on the admitted routes with
   `create_program_address` on canonical bumps stored at account
   initialisation (stored, never caller-supplied without a canonicality
   check). Each authentication then costs one SHA-256 instead of up to 255,
   which removes the runtime's search loop from QV and saves CU (G_R1.8).
   Until it lands, QV keeps the 255-trial bound as a cited runtime premise.
2. The release pins the Agave validator version whose `sol_sha256` and
   `sol_create_program_address` the QV proof cites. The SHA-256 instance is
   the oracle; this pin is a trusted premise stated in the release notes.

## J1.R13 Release-artifact queue (lead)

After G_R1.8 and G_R1.9 land: one SBF rebuild of the guarded release
configuration on the build host (own scope, MemorySwapMax=0), artifact hash
pinned, the CU replay of tx1/tx2 under full random masks rerun once, and the
provisioning harness rewritten for J1.R11 (system-created checkpoint, foreign
buffers). No deployment.

## J1.R14 Order

Unchanged from the status report's six items, with item 6 replaced by J1.R13
and item 5 restated: prove QV for the post-G_R1.8 source. J5 ∥ J2 start when
J1.a and J1.b source closure (items 1–2) land.
