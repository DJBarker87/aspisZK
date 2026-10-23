# S2-Z final handoff

Branch: codex/cx-s2z-20261023. No push. No shipped file changed.
Target: adopted owned AdapterRwModel callers. S2 remains OPEN.

| Field | Disposition |
| --- | --- |
| oracle | Conditional: NativeBinding, RuntimeSyscall, P1Realization; exact total Required14 law additionally needs unrestricted returning-domain hypothesis. See STAGE1.md and S2Z_OracleTotal.total_of_returning. |
| callOrder | Open globally. Owned source value dependencies and checkpoint child digest order proved; native clocks, child/site effects, and transaction history are missing. |
| reachedPrefix | Open globally. Need source-indexed child reached prefixes and the same native save/TX2 history. No invented ranks or independent accepted-run join. |

Proved local results: same-statement decode/validate/encode/verifier cuts from
actual owned acceptance; transported actual op43 dictionary; per-call oracle
implications; exact checkpoint proof/public/checksum append and observations;
returning child consistency including inner Err; countermodels separating
success-only/total oracle laws and value-only/native schedule claims.
These are local/conditional source and model results, not complete native S2.

Assumptions discharged locally: successful decode/validate/afterstate encoding
and first invocation follow from owned TX1 acceptance on one statement;
authentication/encoding/second invocation/emitter values follow from owned TX2
acceptance on one statement. The per-call output representation identity follows
from the existing byte/array roundtrip. Retained/open hypotheses are listed in
STAGE1.md and STAGE2.md. No cryptographic metric, trust item, or existing module
was changed, and no top-level premise-removal/native closure is claimed.

Validation: nine focused host Lean attempts, seven successful (including final
union009); Kani0/60. Failed004/005 were elaboration errors, superseded by changed
sources006/007; failed recovery axioms are excluded. Final union prints all12
theorems with only propext, Classical.choice, Quot.sound. Final target
S2Z_Audit.lean, exit0,2.790292407s,4364592KiB peakRSS,swap0; source revision
d32adf79c8 (dirty new audit source separately SHA-pinned in receipt).
Every run used MemoryHigh6G/MemoryMax8G/MemorySwapMax0/TasksMax64 with host
reservation receipts. No timeout, memory kill, higher cap, unchanged rerun or
remaining job. Exact commands, source/dependency/tool hashes, revisions and
metrics are in manifest.json and lean-*/receipt.json.

Reused: unchanged AdapterRw stage3 objects, lead interface and child proofs.
No Rust/Kani/ELF build or frozen-manifest replay: relevant source/artifacts did
not change; enclosing native predecessors remain open. Stage0's eight source/
interface hashes still match. Adoption pins default d7d42f77…, devnet2b2a9f0e…,
Pool121f3e29… retained; no new binary-to-proof connection is asserted.

Next concrete deliverable: native op43/syscall interpretation plus execution-
indexed actual op10/op11 effect/site ports (including rejection prefixes), SDK
save/write cut placement and cross-transaction account/history retention. Then
instantiate checkpoint/multiproof/S7/S8 joins on these exact source cuts and
bind their sites to c.reached/c.clock. Pure child values cannot supply that port.

Target not yet established. Detailed proofs/limits: STAGE1.md, STAGE2.md;
read-only backend source evidence: backend-inspection.json.
