# Port20ALLOC handoff

Branch `codex/cx-port19rest-20261024`, assigned base
`17d459f0326cff8aa9f55e2629937ca4c5345851`. No merge/push, shipped source,
features, wire, security contract, keys, wallets, RPC or chain change.
Both deployed targets remain **not yet established**.

New concrete progress: Charon extracted the unchanged `heap::filled` body,
the actual row12/row10 LLBC call sites, their complete generic arguments,
and real four-word QM31 Copy/Clone and four-u64 array operands. Aeneas
extracted the helper's reserve-result/post-Vec/resize chain. The actual
returned reserve result controls the error branch; no Bool is chosen by
this source evidence. `audit.json` checks both actual parent calls and exact
whole-file/span bytes against the assigned base. All failure outputs and
input bytes remain in this packet.

**No native helper content/effect law or parent read budget was proved.**
No assumption/budget was discharged, changed or added; no producer is
installed for Port17 OtherBudgets. `INTERFACES.md` states the unchanged budget
predicate and before/after carriers; `OBSTRUCTION.md` gives the precise missing
reserve-state/frame/error/abort and ordered-event association. D157's
allocation-failure/unsafe exclusion remains binding. D189's runtime
private-allocation/abort boundary remains explicit. No allocator/noHash trust
field, Drop erasure or success restriction was introduced.

Charon records hidden allocator parameters/imprecise drops; raw LLBC keeps
conditional Drop and unwind paths. Aeneas omits both parent declarations
from its ordered output despite their retained LLBC bodies. Templates remain
uncompiled `.lean.txt` evidence; their external placeholders are **not** new
axioms in a proof. The standalone harness uses native std runtime, rather than
rebuilding the production no_std crate/artifacts; source inclusion does not
claim whole-crate or SBF identity.

New validation:

| Target | Exit | Wall seconds | time peak RSS KiB | Swap |
|---|---:|---:|---:|---:|
| extract-001 Charon | 0 | 1.207173295 | 229636 | 0 |
| extract-002 Aeneas | 0 | 0.305898657 | 66352 | 0 |
| kani-001 CLI preflight | 2 | 0.004401633 | 4928 | 0 |
| kani-002 full constructor, all Variants | 1, timeout | 120.896533456 | 1631260 | 0 |
| kani-003 admission | 1 | N/A, compiler not launched | N/A | N/A |

Every launched command has its full command, revision, source/tool/sysroot
hashes, preflight/go inventories, capped-scope receipt, time output, aggregate
RSS and cgroup peak. Caps: High1536MiB/Max2GiB/Swap0/Tasks64. Constructor
timeout: no OOM, peak cgroup1690894336 bytes, no retry. Its unsupported-construct
warnings are retained. Kani-003 denied on a disappearing `/proc` entry during
in-scope admission, after two external snapshots passed. No unchanged retry
or cap/service/cache mutation. Pre-monitor admission metrics are explicitly
unavailable, not invented. Final read-only diagnostics find no remaining own
compiler processes. `#print axioms`: N/A throughout; no Lean theorem compiled.

Usage: Lean **0/12** (12 unused); extraction **2/2**; Kani **2 actual command
invocations**, **3/4 conservative charges** including denied admission;
standalone optimized Rust **0/2**; backend builds **0**. Combined soundness
ceiling368 and Port18 reservation unchanged. No full manifest/regression.
Kani-001/002 inherited a generic extraction-oriented expected-time prose
label from the launcher; their exact commands/logs show optimized compilation
then CLI validation/SAT, with no arithmetic elimination. The launcher label
is corrected for subsequent commands; historical receipts are unchanged.

Reused: approved helper/model statements and prior source assessment, not
old compiled-object or ELF validation. Current inherited ELF targets remain
default `f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4`,
devnet `63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299`,
Pool `121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548`.
No new identity gate. Root/A cache coherence remains Port18's task.

Next concrete deliverable: a small native reserve/cleanup bridge under the
existing policy that retains Err, abort/divergence and complete ordered
effects; then the actual constructor control join and unrestricted op12
producer. A successful-allocation-only Kani result would be insufficient.
