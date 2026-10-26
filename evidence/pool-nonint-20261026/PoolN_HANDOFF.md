# PoolN noninterference handoff — budget exhausted, target not established

Branch `codex/cx-pool-nonint-20261026`; worktree cx-pool-nonint. Local commits
only, no push. Initial source anchor e358fbda670328123420f1033d2b948cd69f9597.
No accepted write of attacker-chosen checkpoint bytes was found in this
campaign. The requested exhaustive theorem `PoolN_Frame.all_handlers` and the
individual universal handler-frame theorems are **not proved**.

## Exact established results

- `lean/PoolN_Guards.lean`: symbolic192/1768 versus destination-size exclusion,
  prepared-plan guard rejection and page-length rejection. These are explicit
  guard/source-summary models, not whole-handler source refinements.
- `lean/PoolN_Effects.lean`: exact rejection error, unchanged supplied state and
  complete ordered prior effect list survive guard composition; no arbitrary
  suffix (close/reassign/realloc/CPI included) executes. The actual source
  prefix/effect instance remains required.
- `lean/PoolN_Verifier.lean`: reuse of the existing Hist_/Hiq_/D189 source
  results for V1 occupied zero rejection/no accepted reinitialization, V2
  wrapper's complete heap frame and disabled release admission. All inherited
  SDK, allocator/native/extraction/runtime boundaries retain their scope.
- `lean/PoolN_Nonvacuity.lean`: inhabited length/marker guard shapes, explicitly
  **not** authenticated checkpoint provenance or native reachability.
- `PoolN_LEAN009`: focused axioms audit of every new theorem, only propext,
  Classical.choice, Quot.sound, or none. Current five module sources match exact
  passing receipts. Failed error-elaborated sorryAx outputs are rejected.

Native actual-source Kani results (see exact harnesses and receipts):

| Accepted local result | Evidence |
|---|---|
| Complete ASDI on the valid80-byte request, checkpoint as primary state, arbitrary bytes/balance, exact error, no CPI, pointwise full byte/balance frame | KANI001192; KANI0371768. Fixed input keys/metadata; other account roles/instructions are not generalized. |
| Complete ASPX rejection in core, shard or authority role on the encoded2/3-account layouts, exact error and bytes/balance frame | KANI004192 core sub-result (overall paired run failed);005 shard both;006 authority both;0381768 core. Fixed surrounding layout/metadata. |
| Fresh/PDA, post-CPI, owner/size, plan-close/refund, allocator/WithSeed, token-program, forest master/lane/page, marker and token/mint parser guards | KANI007–022 except008's failed1768 paired member; exact local domains and errors in source snapshots. Most use arbitrary byte index for full pointwise frame. |
| Actual canonical/invariant legacy-state decoders, readonly master, stronger fresh/payer/marker/plan flag/key domains | KANI025–031. These split probes assert exact rejection plus first-byte/balance frame only. |
| Actual copied loop-free stack predicate: every height, exact error/result, both transaction-admission and CPI-rejection covers | KANI036; production body changed by function-name substitution only. Assertion instrumentation isolated after035 timeout. This is not full dispatcher source/ELF closure. |
| Split post-create1768 guard, both preparations at expected384 bytes | KANI039, first-byte/balance frame only; other widths remain separate obligations. |

Native conditional/counterexample scope is not promoted by theorem names or
pass counts. The arbitrary byte-index proofs quantify every byte of the fixed
192/1768 buffer; first-byte-only probes are expressly weaker.

## Failed/unrun obligations retained

KANI002/024: added harness compilation errors (Ref lifetime / vec macro), fixed
in later source variants. KANI003/004/008/023/032/033/034/035/040: timeouts;
original sources and logs retained. None was rerun unchanged or with more time
or memory. Replacements isolated frame observation, parser/metadata classes,
preparation alternatives or loop-free assertion instrumentation, with weaker
classes explicitly labelled. KANI034 full native CPI-builder/metas checks and
KANI040 arbitrary distinct checkpoint-alias positions among14 accounts remain
unproved. KANI035's loop-free scalar gate is superseded by the passing036
instrumentation split, not by a higher resource limit. Broad handler prefixes
023/032/033 remain failures. Other generated prefix fixtures and the dispatcher
control projection are proposals/source artifacts, not verified results.

**Source-order correction:** read PoolN_SOURCE_ORDER.md. AS8D current-page
validation follows note hashing/pair-leaf/append planning; ASPP plan freshness
follows plan construction and possibly a rollover-page CPI. The blanket
“every role rejects before heavy arithmetic” strategy is false as an ordering
claim. This is not a security attack or evidence that noninterference is false.
Preserve the actual earlier child results/errors/effects in the replacement.

## Remaining source joins, by live handler

| Handler | Still required for the requested universal frame |
|---|---|
| AS8I / ASIN | Bind every master/lane/state/page/vault and allocation role to the checked guards, all aliases/counts, prior parser/SDK errors and CPI effects. |
| AS8D | Join master/lane/page/token role guards and every mutation, preserving the actual arithmetic/address/error prefix before page checks. |
| ASQ8 | Join readonly ASC8/CP access with every lane/page/marker/token mutation and exact verifier/System/SPL CPI effects. |
| ASDI | Generalize the checked primary-state request class; prove current/rollover page and token roles and actual prefix effects. |
| ASPP | Join plan/rollover-page guards after actual build/CPI prefixes; no child-success or empty-effect replacement. |
| ASPX | Generalize the checked concrete role/layout classes to all instruction/count/key/flag/borrow cases; bind both close sites to constants and physical accounts. |
| ASPF | Join state/page/marker/token/plan roles, activation/receipt children, close/refund and prior effects. |
| ASPT / ASWD | Bind primary canonical-state and all page/marker/token roles; broad prefixes timed out, so local guard facts alone do not close either handler. |
| Dispatcher / V1 / V2 | Connect the native branch/entry/body/physical-account instances. Existing verifier wrapper facts and the stack predicate retain their original source/runtime/ELF boundaries. |

No `only_AS8C_writes` hypothesis, full lifecycle law, conditional handler-frame
structure or invented `all_handlers` conjunction is introduced. Runtime
ownership, syscall/CPI and rollback semantics remain the instructed external
trust; no additional trust item is adopted. No global release row is removed.
The universal accepted noninterference target and100-bit release target remain
unchanged and not established. The AS8C write kernel remains PoolW_'s job.

Concrete next deliverable: isolate source slices *after* pure parser/owned-child
cuts, prove their account footprints and error/effect composition, then map each
actual write/create/close/CPI site to its same-account rejecting guard. Start
with ASPX's short source branches and the measured local guards. Derive the
per-handler frames and finally the dispatcher conjunction; do not add another
history-only wrapper or treat the supplied prefix model as its own instance.

## Validation, resources and freeze

**Hard stop: Kani40/40 runs used** (29 overall green,11 failed, including paired
partial successes); Lean9/100 attempts (5 green including audit,4 rejected
syntax/recursion elaborations). No dependency build, package replay, full frozen
manifest replay, arithmetic release gate or SBF rebuild. Exact command/target,
source anchor/hash, dependency selection, exit, wall, peakRSS, swaps, caps and
printed axioms are in each receipt and PoolN_attempts.jsonl. Raw source anchors
are retained with dirty=true; PoolN_revision-context records execution worker
HEAD separately. Current sources are authenticated by exact hashes.

Lean sum wall16.553276s, peak4,394,204KiB. Kani sum wall1316.661775s,
peak5,904,840KiB; all swaps0. Per-job scopes enforce6G high/8G max/Swap0/Tasks64;
Lean -M7000; Cargo/Kani opt-level3, debug0, four jobs. No timeout/cap increase,
memory-killed rerun, new launcher or monitoring infrastructure. Proof time is
CBMC symbolic execution/SAT; compilation was optimized and cached. Final host
scope inventory contains no PoolN job; unrelated PoolV/PoolW jobs were untouched.

Coherent workspace/cache:
`/home/dombarker/project-offloads/codex-cx-sound-int2-20261025`;
owned native copy/cache `PoolN_src` / `PoolN_kani_target`. Existing S2W runners
were reused unchanged. Hist_/Hiq_ objects and the inherited Hir_ native source/
cache were reused; no existing proved module or other worker file was edited.
All133 host Pool inputs match frozen production prefixes plus exact cfg(kani)
suffixes. Local132/132/133 inherited compiler inputs match. PoolN_validation.json
checks source/snapshot integrity, scope, profile/caps, exact-source green Lean
receipts and standard axioms. Authored-file whitespace passes; raw compiler
stdout is retained verbatim, including its whitespace.

Shipped repository files, features, Cargo.lock, keys/accounts/funds and ELFs are
unchanged. No rebuild trigger. Inherited ELF hashes, **not newly reproduced**:

- default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4
- devnet63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299
- Pool121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548

Only new PoolN_ Lean modules and this receipt directory changed. No session A,
S1/S3/S4/S5/S6/S9, PoolW_, F3K_, prover-rw, other worktree or remote branch was
touched. No binaries, objects, ELFs or archives are committed. All commits are
local and use plain messages with no attribution.
