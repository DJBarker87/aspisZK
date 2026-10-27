# XRe route C prime handoff

**Target not yet established. Actual top premises removed: 0.**
Branch codex/cx-extraction-repro5-20261027 (actual checkout suffix retained).
No push/merge, shipped change, ledger/contract edit, other worker prefix,
session A worktree/candidate mutation, key operation or ELF change.

## Extraction finding

Three selector-only Charon lowerings, same pinned release source 4bb3b3f51e…,
features/private-leaf-salts, built MIR and identical tool binaries. First two
artifacts are REJECTED (has_errors=true): incompatible Iterator default-method
trait references. The focused third selector excludes Iterator::copied and
produces 8b049f3188cb83227ab485562c755811d33e643fef44a30de5748a3349cae659,
16981964 bytes, has_errors=false. Exactly six release functions opaque; all
other release functions in the selected closure have structured bodies.
XRe_required_bodies.json hashes the named required roots/helpers;
XRe_llbc_inventory.json inventories every non-null function (459/685 slots).
Foreign library opacity is visible, not relabelled as a release proof.

Pinned Aeneas then fails at r1_semantic.rs83/FunsAnalysis.ml134: the semantic
boundary calls excluded Iterator::copied. It emits zero Types/Funs. This is
an unresolved library-declaration/call-closure conflict, not evidence of a
seventh untranslatable release body. All four invocation receipts and errors
are retained; original 80465ea3 and tools remain unchanged. No translator/library
patch, LLBC masking or extra release opacity. Extraction budget 4/4 exhausted.

## P6 and Lean results

Owned safe Rust references exist for all six leaves, with verbatim private
source excerpts and direct public compact calls; no stubs/contracts/unsafe.
XRe_CORRESPONDENCE.md supplies line-level mappings and explicit missing parts.
No complete six-leaf P6 certificate or release association is claimed.

Kani 20/20 used: 9 passed, 10 timed out, 1 unwinding failure.
Passed: E/K checkpoint scalar writers with prefix bytes; header;two roots;
all 22 query encodings;10 alpha encodings; compact check at every length 0..31;
echeck at every length 0..63/both flags; expansion Result and byte frame at
input<=32/output<=64. K019 repairs the test assertion, retaining SAME bounds,
using an arbitrary destination index; no unwind/cap increase. Whole prepared,
selection-carrier/powers, larger compact/wide checks, wide_view at actual lengths,
and 64-weight serialization remain unproved. No timeout is a counterexample.
No timed-out or killed target is rerun unchanged.

Lean 2/100 used: failed focused proof corrected, then XRe_L002 passes all seven
byte/control model theorems. Printed axioms are only propext/Quot.sound or none.
Failed L001's diagnostic sorryAx is REJECTED; final source contains no holes,
axioms, native_decide or heartbeat/recursion overrides. The model preserves
trailing chunks, expansion failure frames/lengths, projected scalar selection,
and three ordered digest calls with explicit state; it is not a complete
arithmetic/borrow/payload model. No top imports it.

Actual release Types/Funs are absent, so concrete XRe_Association.lean cannot be
typed honestly; no phantom release carriers or arbitrary equality callbacks are
installed. XRe_OBLIGATIONS.md names every remaining item in inherited order,
with affected ledger families and estimated target sizes.98 Lean attempts are
unused, not called exhausted: concrete association targets remain unavailable.

## Resources, pins and exact before/after

All 26 attempts terminal; one own capped scope at a time. High 6G / max 8G / swap 0 / 
tasks 64; Lean -M7000; Rust/Kani opt-level 3, j1. All admissions allowed, 0 retries.
Max peak RSS 6508152 KiB; max cgroup peak 6675628032 bytes;
all swaps 0. No memory kill or cap raise. Per-attempt receipts retain command,
source/dependency hashes, revision, exit, wall, RSS,cgroup peak,swap,raw axioms
and diagnostics. XRe_revision_provenance.json supplements configuration-base
revisions with launch checkout heads; exact dirty-source hashes remain primary.
XRe_Verification.json reports no validation error.

Final host audit rehashes all 7978 release files (unchanged), tool binaries,
LLBC artifacts, objects and crate lockfile; records 0 generated output files.
Only own rebuildable Rust/Kani/Lean caches were removed after checking no own
live prover. Pinned coherent workspace and all source/tool/LLBC/evidence artifacts
remain. XRe_Cleanup.json records object hashes/sizes before removal. No binary,
object, LLBC, tarball or ELF is committed.

XRe_Top.BEFORE/AFTER retain COMPLETE identical Rc10_Top.deployed sources,
SHA256 c5c85966b83fbaf24626724fe9becdef92214389fb4286d6ba0d304f486e1527.
Ledger unchanged. Ledger method: quantified atomic families/shared witnesses,
T/P/G/C retained, alias L185=L159 deduplicated; removed/added/changed 0/0/0,
delta T0/P0/G0/C0. No fresh absolute recount, changed quantifier/carrier/failure
event/conclusion/metric/trust item, or weakened target. Frozen3, approved game
and RuntimePersistence retained. Zero/empty local model witnesses and satisfiable
canonical harness domains do not supply a joint same-witness inhabitant of the
actual top premises. Fresh whole-top replay/formatter reachability remain open.

No shipped change means no ELF rebuild trigger. Historical pins only, not newly
reproduced: default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4;
devnet 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299;
Pool 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548.

Next deliverable: a complete pinned extraction preserving the used copied call
and compatible trait signatures, then full P6 stage composition and concrete
Prepared/scratch/powers, geometry/line_z, Dot count, accepted candidate/checkpoint
associations. L187 coherent release replay and source-to-ELF association remain
open. No source-refinement gap is promoted to a cryptographic assumption.
