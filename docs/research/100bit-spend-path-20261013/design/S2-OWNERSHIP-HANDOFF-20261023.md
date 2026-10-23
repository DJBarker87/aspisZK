# S2 ownership transfer — 2026-10-23

S2 remains OPEN. No actual SDK enclosing theorem or 100-bit conclusion is
established. User transfers S2 to another owner; this session now retains S1
and S6 and must not duplicate further S2 work. Frozen production is unchanged.

## Starting point and accepted work

Isolated branch `codex/s126-caller-20261021`, worktree
`/Users/dominic/ZK/.worktrees/s126-caller-20261021`. Do not modify this or another
live worktree from the new session; use an isolated checkout and explicit
imports/cherry-picks. Last green commits:

- `6cec9df76e`: COMPLETE installed borrowed stage1 constructor on ORIGINAL
  full SDK/account records, fixed original proof/public inputs, supplied first
  checkpoint saved in account2, CP-only byte heap update, unchanged account/
  lamport metadata, current verifier child with observer None. See
  `S2-FORWARD-CALLER-20261023.md` and `ReadyRawInputs.construct`.
- `d1c4719462`: native scan probe empty/ghost-only footprints, four kernel
  scanner ghost-erasure/reporting laws and exact WHOLE frozen stage1 body
  erasure. See `S2-SCAN-FISSION-20261023.md`. This closes the local scan-fission
  gate in its checked native input class, not the enclosing SDK join.

Reuse the existing checked native iterator constructor/one-step join and total
std-any extraction/induction; do not rebuild parsing or multiproof work. Existing
native constructor-ready v4, 17 first-entry windows, unseeded complete native/
reference success pairing, copy frame, actual implicit cleanup, region geometry
and source GOTO destruction order are evidence within their stated classes.
They are not yet one concrete same-execution certificate.

## Exact remaining premises

`S2SdkReadyRawInputsV1.construct` has only FOUR successful child-call observations:
`decoded`, `validated`, `encoded`, `firstReturned`. It also requires actual input
metadata/slot/key/counter/length/zero-checkpoint/prefix/tag facts. Derive these
from the SAME actual native accepted run and the fixed external input bytes;
no independent caller/body/write/release success may be smuggled in.

Then identify native output bytes and metadata with the constructed reference:
compose the original copy, actual compiler implicit cleanup, exact region
geometry and source order. The old native/reference pair reads original proof/
public allocations AFTER native execution, so allocation identity alone does
not give original byte identity. Initial-clone/reversed whole pairs and multiple
whole-frame checks timed out; do not rerun unchanged or raise caps.

Retain actual syscall/child interpretation (ops and verifierOps), error effects,
release None, valid heap/allocator/runtime/ABI/P6 and oracle/query trace binding.
Full R22 totality is not established by the accepted-class reference constructor.

Lead interface: `lean/S2LeadInterface.lean`, design
`S2-LEAD-INTERFACE-20261022.md`, last section of
`HANDOFF-SESSION-A-20261021.md`. Required14 fields: proofBytes, publicBytes,
proofSuffix, proofLength, checkpointBytes, checkpointLength, nodeViews,
y1Input, observerNone, reachedPrefix, callOrder, accountFrame, writtenMetadata,
oracle. The actual suffix is [688,58295), length57607. Save/account/TX2/resume
must retain the SAME1768 verifier CP. Pool ASQ8, reconstructed ASF8 and verifier
CP are distinct. Hash equality is not byte identity; collision/query budget
or a proved retention/reconstruction route remains. No new security metric,
collision budget or source adoption is authorized by this packet.

## Latest experiments: EXCLUDED, no closure credit

All artifacts are source-only under
`evidence/s126-current-caller-20261021/`.

1. `sdk-implicit-copy-cleanup-composed/`: v1 codegen failed because the callee
   proof harness was absent. v2 adds the verbatim already checked copy harness
   and uses its verified std-copy contract while all SDK/implicit Drop bodies
   stay actual. The parent still TIMED OUT: exit1,202.187s,6551064KiB RSS,swap0.
   No combined frame/equivalence result. Separate green copy/cleanup evidence
   remains valid; this failure does not refute it.
2. `sdk-live-out/`: output-slot adapters retain the ACTUAL Result/Ref/ProgramError
   types and unchanged SDK call. They try to avoid Kani's unsupported Arbitrary
   generation for a foreign returned guard. v4 conditional bridge CODEGEN
   succeeded: exit0,1.012s,354588KiB,swap0. This is not a semantic proof. Multiple
   compiled metadata fingerprints are retained as candidates, not silently
   pinned as one authoritative historical GOTO binary.
3. Actual output-slot contract checks became expensive even with a ONE-BYTE
   diagnostic. The10MiB,58295-byte and1-byte probes were explicitly stopped on
   formula-growth review, all around6.2GiB RSS, no swap. v3/v5 had compile errors;
   later versions repaired them. No contract passed. Payload size reduction did
   not resolve the issue. Full/limited/diagnostic domains are labelled; none
   supplies whole-stage totality or accepted-class completeness.
4. Most importantly, the raw-output v7 CONDITIONAL BRIDGE FAILED: exit1,2.899s,
   353848KiB,swap0;2/830 checks fail and2/3 covers reached. Failures are shared
   BorrowRef Drop subtraction overflow and SDK counter restoration. A
   selected-property counterexample for `assertion.10` is retained in
   `sdk-live-out/receipts/sdk-live-out-shared-bridge-counterexample-v7/`:
   rawexit10,0.803s,108008KiB,swap0. This is a candidate-contract/representation
   counterexample, NOT a shipped SDK bug. The proposed contract does not safely
   justify the future guard context; diagnose the trace before any further
   adapter attempt. Do not claim byte-havoc + integer-word checks establish
   valid typed Result/guard identity or pointer provenance.

The unit adapter route got past foreign-return codegen only. The new owner
should not infer that it repaired contextual SDK substitution. The existing
real-guard model direct pairs/unary frames also retain their contextual/runtime
qualifications. No opaque or simplified carrier closes actual-source binding.

Audit commands, requiring no prover replay:

```
python3 tools/s126-sdk-modular-20261021/check-ready-caller-packet.py
python3 tools/s126-sdk-modular-20261021/check-scan-fission-packet.py
python3 tools/s126-sdk-modular-20261021/check-sdk-iterator-packet.py
python3 tools/s126-sdk-modular-20261021/check-implicit-copy-cleanup-composed.py
python3 tools/s126-sdk-modular-20261021/check-sdk-live-out-packet.py
```

Every attempt has exact source/tool/command/exit/wall/RSS/swap receipts.
Kani has no Lean axiom report; no new Lean target was run in these failed
experiments. Earlier green Lean audits/pins remain in their packets. NUC runs
used fresh admission, optimized Rust, one compiler job,6G high/8G max/Swap0;
metadata inspections used1G/2G/Swap0. No caps increased. Collector-only failures
(metadata multiplicity and two identical registry copies) launched no proof;
all candidate metadata and original SDK source are retained, not guessed.
One local generator syntax/missing-input preflight launched no Kani proof.

Freeze remains historical b2727acd3abf79315d18b754a260f58f4b1c6326, adopted
25866ec331cc7ce27dd9956609c11d32fa8fa58a with S4 adoption
29cbab431742f7e899870595167efa193a379f0a. Read-only research tip inspected
at e23e12591f. Four caller files remain as recorded by the ready-caller overlay;
transitive adopted source/ELF/runtime re-pins remain obligations, not inherited
from historical evidence.

All jobs launched by this continuation are terminal. A final process query
found no live SDK output-slot or copy/cleanup composition jobs. No source
adoption decision is needed for this handoff. S1/S6 continue in this session;
their eventual enclosing closure still requires the S2 owner's actual binding.

## Follow-up for the new owner: MIR-sensitive stub result (S1 worker)

See `design/S1-CLAIM-SOURCE-STEPS-20261023.md`, MIR diagnostic section, and
`evidence/s126-current-caller-20261021/s1-claim-source-steps/attempts/`.
Same source/harness/Kani0.67: `s1-push-maperr-result-preflight-v1` fails the
explicit expected Error::Parse result under the existing opt3 flags;
`s1-push-maperr-mir0-v1` passes both success/error covers with added
`-Z mir-opt-level=0`, retaining opt3/overflow checks. Full all-six-point
one-step coupling also passes with that setting, including arbitrary Err and
post-state. This is a concrete MIR/instrumentation sensitivity worth reviewing
for source-level stubs. It does NOT establish the cause of the earlier SDK
representation counterexample, and does not reverse route B or change S2.
No new S2 job was launched. Scripts and exact source/tool/resource pins are
available on this branch; do not silently reuse older optimized-stub claims
as proofs of a different operation interpretation.
