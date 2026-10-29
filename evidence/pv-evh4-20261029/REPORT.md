# Partial prover-subprogram world: full task unfinished

Branch `codex/pv-evh-20261029`, exact worktree
`/Users/dominic/ZK/.worktrees/pv-evh`; resume baseline `27b582ca44`.
**Rows removed: NONE. The requested full prover worldRun is not implemented.**
The privacy target is not established. This is an incomplete handoff, not
budget exhaustion or a checked counterexample to the stateful-prover task.

## Delivered and proved

The D520 design addendum was committed at `59edb85f68` before any new Lean.
Its post-proof frontier now distinguishes implemented subprograms from the
unfulfilled acceptance criteria. `effect-world-map.json` preserves all 262
ExternalFuns signatures and textual source call sites, with per-operation
mapping/status. It is a static specification, not transitive native-effect
coverage. The cx2 report and effect interface were read using git show only;
read-pins.json records that branch revision and input hashes. No client port,
reference, opaque plan::prove or new extraction was made.

`PV_EVH_World` defines a state/writer monad retaining Result, post-state and
NativeEvent prefixes on failure and divergence. It records entropy cursor,
file data/durable bytes, oracle history and counters. Allocation and clock
counters are only data; there is no allocator/panic/abort implementation.
Its oracle/count/file projections are generic Run projections. They are NOT
installations into rtDeployed or proofs of the complete prover trace.

`PV_EVH_Entropy.entropyBody_fixed` proves complete Result equality against
ProverRwFull's actual emitted generate_for_mask_nonce_loop.body, under the
uniform fixed-answer view. The entropy call advances its world cursor and
records request/return metadata; nonreturning answers retain the request.
The exact source tail after that call is named afterDraw and remains Result-only.
It is not an arbitrary answer callback, but its other native effects are not
interpreted here. Private seed bytes are not copied into observation events.

`PV_EVH_WorldLoop.fixed_finished` and `PV_EVH_EntropyLoop.entropyRun_fixed`
prove source-loop equality for completed finite evaluations. Exhaustion is
an explicit status, preserving its prefix, and is not called source divergence.
This fixed view is a sufficient uniform-answer domain, not a complete
characterization of per-run partial dictionaries. Reject-then-success entropy
has no such uniform view, as the existing no_retry_then_success theorem states.

`PV_EVH_NonceWorld` supplies typed open/write/sync/options handlers, delivered
and durable file state, request/error events and successful creation events.
Delivery/path/errno adapters remain explicit boundary data. The selected
source spines sync_directory, reserve_fallible and reserve are interpreted in
PV_EVH_NonceSource. Their _fixed theorems prove complete Result equality under
Compatible file answers. reservation_path and other lifted helpers remain
Result-only; allocation, hashing, drop and other internal events are not
claimed covered. Directory crash-persistence/native payload fidelity is not
proved. The generated source fragments and hashes are retained in the two
*-generation.json receipts. Both generators reproduce the accepted Lean bytes.

`PV_EVH_ViewModel.joint_view` constructs simultaneous entropy/file
compatibility for the erasure domain. Its empty byte adapters are labelled
MODEL VIEW ONLY. It proves neither successful proof production nor native
observation adequacy. It is NOT the requested ruling-(v) witness.

## Required work still missing

There is no interpreter of RealR1_client.prove_for_proof_accounts,
prover.retry_attempt or the complete masked-attempt call cone. No full
nativeEvents, attempt/rejection source counts, oracle source prefix or complete
nonce-store/fileTrace binding has been installed. No allocation/panic/abort
source interpreter or full NativeTrace terminal conversion is supplied.
D520_client_before_OPEN and D520_client_after_OPEN explicitly remain inputs.

No successful full prover world, opsNative installation, publication join,
or actual-domain non-emptiness is proved. NativeObstruction62 was inspected
read-only: it prevents inferring uniform capture, and advancing world state
alone does not resolve its open op132/non-emptiness obligation. Ruling (v),
and (v') where actual families are used, remains unfulfilled. No privacy
skeleton or decomposition credit is claimed.

Before/after: the same 19 runtime selections and all privacy/deployment
premises remain open. No endpoint theorem, trust field, simulator, observer,
native alphabet, frozen source or release artifact changed. New Compatible/
FixedView hypotheses belong only to local erasure lemmas; they are not new
privacy trust or a discharge of observation. Entropy laws still map to the
existing entropy_law/entropy_kernel, observation adequacy to observation;
V370, V371, rdea-1, V400/V396, D159/D166 and L1/L2/L3 are retained. No formatting
or Rust/native fidelity credit is claimed from the imported Aeneas models.

The remaining prover work is an implementation/proof frontier, not an owner
permission blocker. D520 concerns the client and is not a reason to stop the
prover task. No host/cohort obstruction remains as justification for task
completion, and the unspent budget is reported explicitly.

## Validation and resources

Seven subprogram modules, one axioms audit and one new-closure import replay
passed. The audit prints all 26 new theorems; every accepted axiom set is a
subset of propext, Classical.choice, Quot.sound. Failed elaborations' sorryAx
recovery output is retained only in failed receipts and receives no credit.
The replay is ONLY the new subprogram closure, not the frozen privacy release
manifest. No release result or complete privacy regression is claimed.

| Accepted target | ID | Wall | Peak RSS KiB |
| --- | --- | --- | --- |
| PV_EVH_World | 73604 | 0:02.68 | 2618540 |
| PV_EVH_Entropy | 73614 | 0:03.60 | 2616464 |
| PV_EVH_WorldLoop | 73616 | 0:03.41 | 2607656 |
| PV_EVH_EntropyLoop | 73617 | 0:02.48 | 2597900 |
| PV_EVH_NonceWorld | 73619 | 0:04.74 | 2615704 |
| PV_EVH_NonceSource | 73621 | 0:05.61 | 2626648 |
| PV_EVH_ViewModel | 73622 | 0:03.38 | 2606204 |
| PV_EVH_WorldAudit | 73697 | 0:02.44 | 2595704 |
| PV_EVH_WorldReplay | 73698 | 0:02.88 | 2597224 |

Every actual compile used -M7000, MemoryHigh=6G, MemoryMax=8G,
MemorySwapMax=0, TasksMax=64, same-shell admission and zero swaps. Each receipt
records exact target, source revision/blob/SHA, dependency fingerprint, exit,
wall, RSS, swaps and axioms. There was no memory kill. The heartbeat failures
were split/restructured without raising limits. The original env-J external
authority and source-pinned project cohort were verified before loading;
h6'' first-root resolution and plain project copies were recorded. No external
authority extension or other-cohort mixture was used. Own accepted objects
were reused rather than rebuilt. Cache/source/companion data remain in the
existing host workspace for continuation.

The source-only failed-elaboration guard is compile.py, SHA-256
`7a31568d638bf6170122324620bd40ebde33fa54607400449fdf47267368dd7a`. No failed source was resubmitted unchanged. Initial staging
mistake 73605 was pre-compiler (external Init incorrectly checked as a private
project copy), corrected and recorded before the next launch. It is uncharged.

Procedural deviation: early admission retries advanced to new IDs using the
superseded (d) rule. Ruling (m') requires the SAME unlaunched ID. The wrapper
was corrected; 73622 was retried with the same ID and full cooldown. The seven
skipped refused IDs remain unconsumed (id-policy-correction.json). Nine
admission refusals are retained, all uncharged. This did not launch a compiler
on a refusal or shorten a cooldown; accepted scopes had allowed:true/exit 0
admission. No out-of-block ID was used.

Usage: **17/100 Lean attempts: 9 passed, 8 failed; 0 native; 0 Kani.**
IDs used: 73604, 73607–73612, 73614, 73616–73622, 73697–73698.
The 83 remaining Lean attempts are unspent. Full task acceptance was not met.
No wallet, key, account or funds operation occurred. No crates/programs or
other worktree changed. Nothing was pushed. audit.py validates the receipt
chain, source hashes, proof discipline, IDs and file sizes; validation.json
records its result. commits.txt is the stage log through the pre-handoff
snapshot; a final evidence-only commit follows that snapshot.

## Next concrete deliverable

Extend source-directed interpretation through the exact proof-account callback,
retry owner and masked-attempt callees, including every effectful external,
allocation/runtime path and callback continuation. Existing Result-only helper
calls must not be promoted to event-producing source laws. Prove the source
Result transport on its actual compatible domain, install complete prover
projections with D520 client inputs still explicit, then construct the joint
successful proof/publication world at opsNative. Until that is done, no row
removal or ruling-(v) completion is justified.
