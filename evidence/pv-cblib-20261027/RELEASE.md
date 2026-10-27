# Third library closure pass

Branch codex/pv-cblib-20261027, resume base 7aebfd030c. Target not yet established.

Candidate supplied callback laws **5 → 7**: V177/op25, V179/op28,
V180/op29, V181/op30, V182/op31, V185/op34, V186/op35. The stable prior
publication is retained; `PV_CBL_AppendBundle` publishes all seven together.
OPS.md records each route (P6 / extraction), exact source hash and receipt.

## Premise accounting

Before: op30/op31 are arbitrary callback fields in the prior dictionary.
After: the additional selected dictionary installs the checked empty-byte
String constructor and extracted byte-append/UTF-8 transport references.
Full Aeneas Result outcomes are preserved. Native gates are bounded:
capacity n≤4; append valid UTF-8 initial length2/tail length1. Source-image,
allocation/world effects, separate extraction/Kani toolchains, and unbounded
native/deployed association remain explicit. No arbitrary invalid UTF-8 or
oversized Lean String is asserted to be a valid native Rust input.

Canonical endpoint/deployment premises removed: **0**. T remains exactly
entropy_law, entropy_kernel, observation. No simulator, observer, trust field,
security contract or frozen production source changed. E1/E2, RunJoin,
L1/L2/L3, client and coherent repository/deployed closure remain retained.

## SHA block composition

`PV_CBL_SoftBlockSource.source` proves the complete extracted owned soft
word-block result on arbitrary state8/input16 arrays against sixteen
conventional four-round groups, canonical schedule recurrence, pinned
constants and feed-forward. `PV_CBL_SoftBlocks.composed` and
`PV_CBL_SoftBlocksAppend.source_append` prove the word-block fold and
concatenation composition. Rust fallback bytes are checked modulo the
previously documented namespace/positive-shift literal ports.

The owned constructor is byte checked against Sha256VarCore::new with
field-identical carrier/error and exact constant substitutions; extraction,
all-size Result totality, unsupported sizes and zero counter are proved.
This is not the op217 generic default/buffer wrapper.

Fixed-size safe padding reference extraction succeeds after replacing the
eight-byte suffix loop with explicit assignments. Lean proves its zero-fill
loop totality by decreasing fuel, suffix totality, and full Result totality
for pos<64 with exact first-output/retained-buffer equality and reset pos 0.
The separate padding model proves lengths, one/two-block branch/count and
retained-buffer shape. Full content refinement to that model, actual buffer
loan/callback/destructor semantics and the byte-loading driver remain open.
**No V231–V238 digest row is credited. No SHA-NI theorem is claimed.**

## Dispatcher decision

The pinned x86_64 default/std build uses the runtime x86 dispatcher. On the
measured Intel Core Ultra 7 155H, SHA/SSE2/SSSE3/SSE4.1 are present, so the
measured default build executes SHA-NI. A uniquely associated deployed
native prover artifact/CPU is not supplied, so arbitrary deployment branch
selection remains conditional on those pins.

`design/PV-SHA-DISPATCH-20261027.md` records the exact `sha2/force-soft`
proposal, verifier/SBF invocation isolation, intrinsic/ISA/compiler proof
cost under capped T, alternative routes and recommendation. No shipped
build changed and no full timing gate ran.

One optimized S2 transfer fixture produced 57,607 bytes and **3,149,033 SHA
callbacks**. A source correction subtracts three fixture-secret hashes and
adds one production durable-ledger hash: 3,149,031 SHA calls per corresponding
steady attempt, not a universal retry-inclusive bound. Seven-sample,
segmentation-preserving release microbench medians give **7.9110×** weighted
soft/native ratio and **+5.92613 s** projected prove cost. Historical
13.63/13.98 s baselines project to 19.556/19.906 s (+43.48%/+42.39%). These are
shared-host estimates, not end-to-end gates or formal cost bounds.
Recommendation: retain SHA-NI and prove its refinement; do not adopt soft
under the current 15 s / +10% gates on these measurements.

## Remaining std/alloc frontiers

Op26 native Unix join passes arbitrary byte lengths 0–2; complete reference
loan/destructor extraction remains open. Op33 borrowed extraction exposes
an absent/foreign Vec.remove leaf; no invented leaf is installed. Its
small u32 gate timed out. Op36 success diagnostics hit a memcmp unwind
bound; a changed first-run N=3 rejection gate passes lengths 0–2. The full
1024-QM31 success/loan/destructor association remains open. Op32 retains
its exact allocator-effect deferral in NATIVE-EFFECTS.md.

## Verification and custody

Lean attempts: **100/100** (92 standard-axiom accepted, 8 rejected); Kani: 6/6 (four passes, one timeout, one unwind
failure; no checked ROW counterexample). The three reserved audits pass. The final manifest imports 243 modules and
checks 735 explicit declarations; all printed axiom sets are subsets of
propext, Classical.choice, Quot.sound. All 244 current own modules have
accepted source-hash-matching receipts. RESUME8-RECEIPTS.json is the new pass index;
RESUME-RECEIPTS.json and TALLY-resume2-prior.json retain the preceding pass.
All raw rejected attempts remain. 41604 hit the internal 7 GB limit; 41606
was stopped as memory rose. Named symbolic boundaries replaced the proof;
no cap or recursion/heartbeat option was raised and no failed source was
rerun unchanged. Both padding interpreter failures remain as evidence;
the extractor was not changed.

Only assigned Env-J IDs 41588–41799 are used once. Last three charged Lean
attempts are reserved for callback/selection/own-manifest audits. The final
manifest is an own-module replay, not a repository-wide/deployed replay.
No production crate/program change, ELF rebuild, push, merge, wallet/key
creation or cleanup occurred. 244 accepted own objects are retained in the pinned host lean-objects cache.
Own kani-target, charon-target and dispatch-target scratch were removed after
checking no active target processes. No shared /tmp sweep was performed;
unattributed solver remnants are not assigned fabricated ownership.

## Next concrete deliverable

Integrate the seven bounded candidate laws without dropping their native
association limits; prove the fixed padding content/source-wrapper link,
byte compression driver and digest wrappers, then the SHA-NI/dispatcher
instruction/source/compiler/deployed association. Target not yet established.

## Final audit receipts

Source freeze `2c21958db216da160c9f160b5a438934c255caf5`. Every final
row exits 0, swap 0, standard axioms only; exact commands/dependency hashes and
full #print output are in the numbered JSON/log files.

| ID | target | wall | peak RSS KiB |
|---|---|---:|---:|
| 41797 | R1Z/PV_CBL_Resume8CallbackAudit | 0:02.37 | 2627708 |
| 41798 | R1Z/PV_CBL_Resume8SelectionAudit | 0:03.99 | 2624784 |
| 41799 | R1Z/PV_CBL_Resume8Manifest | 0:03.27 | 2645688 |

Env-J used IDs: 105, all unique, including 5 uncharged admission
refusals. Reserved 41797–41799 were the last three charged attempts. The next
unused assigned ID is 41690 (41690–41796 remain unused); 41797–41799 must never
be reused. Work stopped on exhaustion of both authorized budgets. No checked
ROW counterexample was found.
