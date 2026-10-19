# J1 lifecycle invariant source inventory

This is a source-level inventory of the `r1-cost-probe` pool-adapter lifecycle at repository revision `5dba4e4266ec6eebceb9adf49d60db5e5695bed3`. It records guards and write ranges relevant to two proposed invariants; it is not a proof that either invariant holds for all executions.

Full-file SHA-256 pins at that revision:

| File | SHA-256 |
| --- | --- |
| `programs/r1-cost-probe/src/r1_pool_adapter.rs` | `b2adab8610189a5031fc6f28a7cdeef12c01aa292423743cb4696aa3ee1590a4` |
| `programs/r1-cost-probe/src/lib.rs` | `36d36ee707f565df675db2ef7b2d27467f8b79bb99142c4b21d6fb7cc81910c9` |

The later release-guard change at `98c316524` is separate. Its `lib.rs` SHA-256 is `65ffe02678f80509759f4828c62439f075b3edbcc8dc3a2f5f58dd3256d6e30d`, and its `pool_route.rs` SHA-256 is `43cfa25ec59e5349773599924d318a4b8fda923c4958760fcf1482d8fb2db9f0`. There `pool_route::admitted` admits exact `[3,10]`, `[3,11]`, or an `ASQ8` prefix (`pool_route.rs:3-5`), and `process_r1_cost_probe_instruction` rejects other inputs before account access (`lib.rs:33-42`). At `5dba...`, the entrypoint also forwarded tags 4, 5, and 6 to the adapter (`lib.rs:31-37`). Thus the lifecycle below was reachable in the inventoried source revision and is excluded by the later outer guard.

## Lifecycle account and dispatch conditions

`r1_pool_adapter::process` dispatches first-byte tags 4, 5, and 6 to `lifecycle_init`, `lifecycle_write`, and `lifecycle_finalize` (`r1_pool_adapter.rs:982-993`). It has no CPI calls; the only mutable account-data borrows in this module are in the three lifecycle functions and stage 1 (`rg` check of this pinned file). The lifecycle handlers take exactly two accounts through `lifecycle_accounts` (`:181-204`): distinct target and authority; target owned by this program, writable, nonsigner, nonexecutable; authority readonly, signer, nonexecutable, with nonzero pubkey. This prevents target/authority aliasing for these calls. The function bodies make no other account references.

The header is 40 bytes (`:51-55,87`). Header validation requires exact body length and either (a) unsealed authority bytes equal the supplied nonzero signer key or (b) sealed authority bytes all zero (`:207-239`). The zero sentinel therefore cannot satisfy the unsealed-authority check.

## Mutations and guards relevant to the proposed invariants

1. **Initialization (tag 4).** Input must be exactly `[4, kind]`, where kind is Proof or Public (`:276-286`). Before writing, it requires exact total account length and every byte zero (`:291-294`). It then writes only magic bytes 0..4, encoded body length 4..8, and authority bytes 8..40 (`:295-298`). This rejects reinitialization after the header has been set, including after finalization, because the account is no longer all-zero. The body remains zero immediately after init.

2. **Chunk write (tag 5).** Input must include a nonempty payload after the five-byte tag/offset prefix (`:302-316`). It first validates the unsealed header against the signer (`:317-320`), computes the write end with checked arithmetic, and enforces `end <= writable_prefix_len` and `end <= body_len` before obtaining the mutable borrow (`:321-327`). The absolute range copied is `[40+offset, 40+offset+payload.len())` (`:328-335`). For Proof, `writable_prefix_len = verified-afterstate bytes + S2 proof bytes`, while `body_len` additionally includes the 1,768-byte checkpoint tail (`:111-127`, `:51-55`). Consequently this handler’s permitted proof-body writes stop immediately before the checkpoint tail. For Public, the entire terminal-statement body is writable. A finalized account has zero authority bytes, so it fails the unsealed-header check before any body write.

3. **Finalize (tag 6).** Input must be exactly `[6]` (`:338-347`). Before mutation, it requires a matching unsealed authority/header and validates the final body (`:348-353`). For Proof, the final-body validator parses the candidate afterstate and S2 proof and requires the entire tail region to have length 1,768 and contain only zeros (`:242-265`). For Public, it decodes and validates the terminal statement (`:267-271`). The only write after those checks is zeroing authority bytes 8..40 (`:354-359`); neither body nor proof tail is written.

These paths give the source facts a proof would need for the proposed invariants: sealed-body mutation would have to pass the unsealed-header check, and tag-5 writes cannot reach the Proof tail; finalization also checks that tail is zero before sealing. They do not themselves establish an all-history theorem, account ownership across arbitrary programs, or the exact runtime transaction model.

## First stage-1 mutation and failure behavior

Stage 1 is a distinct instruction (`[3,10]` or `[3,11]`) and is the only other mutable borrow in this module (`:868-937`). It requires two distinct accounts owned by this program: writable nonsigner proof account and readonly nonsigner public account (`:868-884`). It requires the public account to have a sealed ASRU header/body (`:886-893`) and validates the ASPU proof header, candidate, proof variant, and zero checkpoint tail before computing the checkpoint (`:899-929`). After the checkpoint is computed and its exact expected length checked, its sole account-data mutation copies it into the tail (`:929-933`). This is why the tail claim is scoped to *before the first successful stage-1 write*; stage 1 is designed to change that tail.

The source orders all fallible checks before that copy. Once copied, the function only logs and returns success (`:930-936`). For failures in any instruction, Solana transaction rollback is an external runtime property rather than something proved by these functions; the proposed whole-history argument must state how it models that property. No lifecycle handler performs a CPI or calls stage 1. In the enclosing transaction, account aliasing between stage-1 proof/public inputs is rejected (`:872-884`); lifecycle target/authority aliasing is rejected separately (`:192-204`).

The source scan found no other mutable write in `r1_pool_adapter.rs` that changes the ASRU/ASPU body: lifecycle init writes only the header, lifecycle write is range-limited as above, finalize zeros only authority, and stage 1 writes the proof checkpoint tail. The instruction-level guard at `98c316524` makes tags 4–6 unreachable through the public `r1-cost-probe` entrypoint, but does not alter these internal function bodies.
