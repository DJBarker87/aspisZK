# NCO composition pilot handoff

**PILOT RESULT: partly; no complete vertical native slice. Do not switch all lanes.**
S2 and the deployed100-bit target remain OPEN. Branch
`codex/cx-native-cpilot-20261028`; commits are local, no push or merge.

## Exact claims established

- Frozen `r1_wire::row_shape` / `compact::compact_row` have passing body
  contracts, passing substituted callers and matched failing controls
  (K048–K055). Their safe Rust references were actually extracted; the new
  NCO_ScalarBridge / NCO_ParserShape theorems identify them with the compact
  and PrefixAggregate cohort definitions on all u8.
- K058/K059 establish the actual `expand_values` contract and wrong-ensures
  control on ONE16→32-byte window, with exact KMX replacements and K056/K057
  copy controls. They do not establish the full leaf domain or a caller join.
- NCO_ValidateModel.reference (L058) proves the complete Aeneas-extracted
  safe validator reference equals the LPl kernel leaf on ALL payloads≤3712,
  including tails/noncanonical inputs and the same first failing row/index,
  after an explicit nominal error conversion. Kernel target:
  `_root_.r1_wire.validate_record_fields`; error carrier:
  `LPl_Kit_Release.r1_wire.Error`. This does not identify the distinct raw
  PrefixAggregate validator, nor prove the frozen native body contract.
- NCO_CallerDomain.validator derives the reference's full3712 cap from the
  same row shape, record length and drop5 slice. NCO_Domains proves why
  the pilot's narrower native domains cannot be used at row25.
- NCO_Framing and NCO_ParserAt prove only the printed invalid-row,
  wrong-length and range-get-None mathematical branches. The complete
  accepted parser/reference equality is OPEN. The failed general caller
  composition draft is retained as TEXT ONLY, not an accepted module.

No headline/native implementation premise, security assumption or runtime
trust item is discharged, added or changed. RPx_Deployed.deployed, L154's
statement-parameter classification, frozen3, RuntimePersistence, the approved
two-transaction game and narrowed D188 remain unchanged. No XRn stand-in,
field-multiplication proof/stub, SHA unfolding or Option<fn> credit is used.
Coherent dictionary digest/error positions remain op43/op44.

## What blocked native composition

Kani0.67.0 rejects `stub_verified` generation of returned `&[u8]`,
`Result<&[u8],...>` and `Vec<u8>` because `kani::Arbitrary` is missing.
K011/K014/K016 are shape probes; K039/K044 demonstrate the real parser edge.
These are compiler failures, not the required failing assertion controls.
Other slice/Vec controls detect inverted ensures/modifies errors and check the
real body, but the families are not admitted for substitution.

K060's one-chunk validator body, K062 inverted control and K063 weak body
TIMEOUT. K061's substituted caller PASS therefore has NO native credit;
K064 likewise uses an unproved weak contract. A bridge runner must gate
callee proof/control/domain closure, not trust the annotation's word “verified”.
The restricted parser body splits also time out. No timed-out result is a pass.

## Budgets and final audit

**70/70 Kani configured invocations,60/60 Lean compiles,6 extraction attempts.**
The exact invocation ledger is NCO_ATTEMPTS.jsonl; NCO_RESULTS.json is its
readable classification. Native:24 PASS (qualified individually),23 check
failures,16 compiler failures (11 own setup errors;5 return-shape barriers),
7 TIMEOUT. Counts are not closure counts. NCO_DEVIATIONS.md records own
input repairs, failed shapes and procedural deviations; none is hidden.

Final target `NCO_Audit.lean`, L060: exit0, wall1.119898627 s,
peakRSS2635468KiB, swaps0, source revision recorded in its receipt and exact
source hash snapshot. It imports the25 prior accepted modules and audits all52
new explicit top theorems. Every printed axiom set is a subset of
[propext, Classical.choice, Quot.sound]; no failed/sorryAx draft is accepted.
This is one focused audit against pinned coherent objects, not a frozen
release replay. No unchanged full regression was repeated.

Every prover/compiler scope uses MemoryHigh6G/MemoryMax8G/MemorySwapMax0/
TasksMax64, one at a time; Lean-M7000; optimized Rust. Admission requires
exit0 AND allowed:true, as archived. All70 native invocations validate the
frozen resolved graph offline and check the unchanged frozen lock afterward.
No cap or timeout was raised. Formal target/command/source/dependency pins,
exit/wall/RSS/swaps/axioms are in each receipt and the JSONL.

## Extraction, objects and source pins

Reference Rust is retained in NCO_harness.patch and per-attempt receipt
snapshots. E004/E006 use matching XRa tools: Charon SHA256
`daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8`,
Aeneas b59d5188 extended SHA256
`c0cf4fccb0879db4ce342da991f6215732a19fc01345b9eec84e632f4673b958`,
Rust toolchain nightly-2026-09-17, --release/--offline/--jobs1. Full commands,
Rust reference/Lean output hashes, tool pins and E006 LLBC are retained.
E005's unresolved Option::ok_or template is TEXT ONLY; E006 includes the
actual library body, removing that gap without an axiom. E002's independent
slot-offset array-borrow extraction failure remains OPEN.

Own host workspace:
`/home/dombarker/project-offloads/codex-cx-native-cpilot-20261028`.
Retained cache:
`/home/dombarker/project-offloads/codex-cx-cpilot-cache-20261028`.
It was seeded by COPYING the two read-only caches; imported and selected
hashes are in NCO_SOURCE.json. All222 resolved Aeneas library objects were
pinned/checked on Lean attempts. The final audit additionally checks767
selected objects, the coherent model roots and imported caches. NCO_AUDIT_PINS
records source/object/tool/coherent-manifest fingerprints.

Postflight rechecks all767 pins, finds no own process, retains the cache and
moves own objects into it with the old object path preserved by symlink.
Only own Rust targets/temp scratch are removed; shared /tmp is untouched.
NCO_POSTFLIGHT.json records paths/bytes/object hashes. No cache or key deleted.

Frozen Rust is4bb3b3f51e16b4525f1d10336e2b0bcbbd775387.
The scratch audit examines496 frozen crates/programs paths:491 exact,3 with
ONLY cfg(kani) instrumentation,2 inherited missing RealR1 client files under
the disabled r1p-check feature. Full diff/attempt variants/source pinsets are
retained as patches/JSON; all selected graph features are recorded.
The unchanged S2W backend copies were hash-compared to SInt2. No shipped
repository file, session A worktree/candidate or other lane's prefix changed.
No ELF rebuild was triggered. Inherited, not reproduced, hashes:

- default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4
- devnet 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299
- Pool 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548

## Remaining obligations and next work

The matrix NCO_SLICE_BRIDGE.md gives every unit-10 function separately.

1. row_shape/compact_row: standalone packet complete; installation into a
   larger frozen caller still requires that caller's Kani contract/domain proof.
2. validate_record_fields: native full-domain contract and matched controls
   require new Kani work. Stage the decoder/word callees or an admitted loop
   contract method; do not replay the32-byte timeout unchanged. The full LPl
   reference equality is now available. The distinct PrefixAggregate-model
   transport is an additional Lean obligation.
3. expand_values: full source/destination lengths, error/frame relation and
   usable whole-function contract require native iterator/window association
   plus the permitted Lean induction. The one-window predicate has no complete
   new extracted functional-reference equality. Both budgets are exhausted.
4. parse_record: complete native body/callee contracts and borrowed return
   substitution require new Kani/tool support. Accepted/tag/header/validator
   model equality also requires a fresh Lean allocation; partial rejection
   theorems are not that equality.
5. parse_record_at: same borrowed-return barrier and unproved caller contract
   require Kani. General model composition remains OPEN after L059 (the
   default simplifier changed the monadic goal into implications; use an
   explicit bind/map proof), and needs fresh Lean budget.
6. Prefix::parse/payload/record/validated_record and ValidatedRecord::framed:
   native borrowed/aggregate interfaces and their actual callee contracts
   require Kani/tool capability. Their references/model equalities were not
   completed; payload has no direct cohort counterpart in the inventory.
7. expand_semantic: full expansion callee domain/contract then one native row
   iteration and source-position/frame association require Kani. Never
   whole-buffer unroll or substitute the16/32 contract at1856/3712.
8. slot_offset: fix/isolate the safe reference's array-borrow extraction and
   prove the scalar loop model; native iteration/caller association needs Kani.
9. ValidatedRecord::row: independent native scalar contract/control remains
   for fresh Kani budget; its own model reference was not constructed. It is
   outside the chosen vertical chain and cannot repair the caller barriers.

Both budgets are exhausted, so no further Lean-only work is being silently
abandoned because Kani alone ran out. The listed model gaps are explicitly
open as well. Next deliverable is a repaired typed return/loop contract route
with fidelity controls, then ONE complete parser slice before wider adoption.
No new trust item or release-target change is recommended by this packet.
