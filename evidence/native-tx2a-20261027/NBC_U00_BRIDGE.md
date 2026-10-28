# NBC U00 release runtime leaves — OPEN

S2 and the deployed 100-bit target remain not established. This packet closes
three local release no-op members and supplies partial model laws for three
others; it does not close U00 or remove a headline premise. Headline:
`AspisR1.RPx_Deployed.deployed`; L154 remains a statement parameter. Narrowed
D188, frozen3, the two-transaction game and RuntimePersistence are unchanged.

## Frozen target and cohort selection

Frozen Rust `4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`. All six member file/body
hashes, lines, calls and NBI2 cohort locators are retained in NBC_TARGETS.json.
Native scratch starts from 1,234 individually checked frozen files, including
the frozen Cargo.lock. No repository crates/programs file changes.

The requested coherent SInt2 object `AdapterRwModel.olean` is pinned by
`evidence/sound-int2-20261025/object-source-manifest.json` to source SHA256
`e09bfc695970e18f47abacb6dcb6d43820c100dfaf68e54f6923dd84c69cc46d`, immutable
revision `d346dc7cb7232f12c4ff930d1e2db320bdc101d9`. Its digest/error slots are
op43/op44. The NBI2 locator instead selects source
`b038de19d4d40d2a62ca1fc27b270d291c66e75eff8462e1846826496b28b133`, whose
digest/error slots are op48/op49. In the coherent object op48/op49 are account
decoders. NBC_L001 type-checking exposed this discrepancy. No shared source,
object or NBI2 artifact was repaired. NBC_COHORT_FINDING.json records both pins;
NBC_COHORT_AdapterRwModel.lean.txt is recovered by git show from the immutable
revision, without reading session A's live worktree.

The successful NBC module explicitly uses the coherent SInt2 slots. It does
not silently identify the differently pinned sources or install a new
headline dictionary. This is a source-locator finding, not a shipped bug.

## Member domains and exact results

| Frozen member | Status and evidence | Exact domain and remaining obligation |
|---|---|---|
| `observer` lib.rs:36–39 | CLOSED local release member: K002; `NBC_ReleaseLeaves.observer` | cu-profiling absent, all caller states; actual native returns None. Cohort theorem quantifies arbitrary coherent Ops. No observer-None hypothesis is supplied. |
| `mark` verifier.rs:31 | CLOSED local release member: K001; `NBC_ReleaseLeaves.mark` | None and every release Phase, including arbitrary usize/u8 payloads. Native returns; exact source has no effect without a callback. Domain comes from actual release observer, not from arbitrary Some callbacks. |
| `value` trace.rs:6–11 | CLOSED local release member: K003; `NBC_ReleaseLeaves.value` | prover absent, arbitrary tag/index and all eight raw u32 coordinates, hence also canonical inputs. Native release body is `let _ = (tag,index,x)`; cohort is ok unit. No field operations or U01 producers are invoked. |
| `filled` heap.rs:5–10 | OPEN; `NBC_Filled.result` is model-only | Arbitrary Copy T, Usize n, same fill value; the Copy clone law and reservation outcome are explicit. Existing NP6 proof yields the entire replicate vector or Allocation error. Native reserve/resize/control-flow/ownership/effect association on that SAME native vector is not constructed. No Kani whole-vector loop was attempted. |
| `SolanaDigest::digest` lib.rs:13–15 | OPEN; `digest_result` / `digest_installed` are local model laws | Arbitrary ordered parts and arbitrary hashv Result replies, including fail/div. Exact reified wrapper equals that hashv call. No native wrapper-call trace/dictionary association to the adopted cohort slot, SAME hashv state, or ordered oracle-effect transport is proved. The local dictionary installation is a definition, not evidence of adopted installation. |
| `error` lib.rs:40 | OPEN; `error_installed` is a local value law | All release verifier errors. A locally defined op44 returns InvalidInstructionData. Native msg!("r1:error:{:?}",e) effect and its association to the SAME error/caller boundary are unproved. NBI2's named error counterparts are verifier-enum carrier conversions; they do not prove this program wrapper. |

K001: 0/10 failed, 1/1 covers. K002: 0/7 failed, 1/1 covers.
K003: 0/0 failed, 1/1 covers. K003 is native reachability/termination evidence
for a body erased to a no-op, not an independent output-equivalence assertion;
the value equality is the checked Lean theorem plus exact release source shape.
No three-member result is promoted to an enclosing U00, S2 or headline theorem.

## Validation, failures and retained boundaries

L001 rejected the wrong coherent slot types and a wrongly qualified WideExact
name. L002 corrects only NBC's source to the actual coherent types/slots and
passes. L003 rejected a missing namespace qualifier; L004 corrects it and
passes. Recovery sorryAx diagnostics in rejected attempts are excluded.
L005 is the final co-imported audit of all seven new theorems; accepted audits
use only propext, Classical.choice and Quot.sound, or a subset.

Every native run freshly validates resolved package tuples/edges against the
frozen lock, runs offline/optimized, and records unchanged before/after lock
hashes. These three runs introduce no stubs, so no field multiplication or
unpaired arithmetic stub is credited. Existing LPb stages are not reused to
claim closure here; no drift exemption is needed. NBC_STUBS.md records this.
One admitted scope at a time; reservation requires exit0 AND allowed:true;
6G high/8G max/swap0/tasks64, Lean -M7000. No timeout, memory kill, rerun,
cap increase, full manifest, SBF rebuild or full regression occurred.
Exact commands, targets, revisions/source hashes, dependency objects, wall,
peak RSS, swap, axioms and errors are retained in each NBC_K/L receipt.

The remaining U00 deliverable is the native reserve/resize association and the
native digest/error call/effect association at the precisely pinned cohort
boundary. The source-locator discrepancy must be resolved explicitly before
claiming NBI2's named-source correspondence. U01/U02 remain held by the ordered
U00-before-U01-before-U02 requirement; their reports enumerate every open member.

Runtime/SHA256/allocator/SDK laws, extraction/ABI/source-to-ELF association,
RuntimePersistence, adversary, event, metrics and artifact adoption are retained.
No new cryptographic or runtime assumption is added; no premise is removed.
Inherited artifact hashes, not newly reproduced: default
f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4;
devnet 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299;
Pool 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548.
No repository cfg(kani) or shipped file changed, so the rebuild trigger did
not fire. No key operation, other-worker edit, merge or push.
