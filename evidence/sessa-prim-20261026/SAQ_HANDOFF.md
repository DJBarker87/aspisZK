# SAQ primitive handoff, 2026-10-26

Status: source-selected replacement checked; actual generic Rc2 integration
remains open. Budget exhausted: 100/100 Lean compiles, 0/20 Kani. No push.

## Before and after

Before: `AspisR1.Rc2_Top.deployed`, specialized to the same source-selected
dictionary, requires query `SessionAPrimitives` as its `primitiveOwner` input
and retains canonical/domain/mul/one/inverse guards in its returned outcome.
After: `AspisR1.SAQ_CompleteTop.deployed` derives that input and removes those
guards from `SAQ_CompleteResult.Outcome`. Its remaining inputs and inherited
conclusions are retained at `SAQ_CompleteInstall.configuration indexError c
reservation`. The new `indexError : CoreError` parameter is source-constructor
data in the existing error carrier, not a new correctness proposition.

The selected dictionary replaces the assigned free primitive callbacks with
source bodies and their existing carrier bridges. This is not a proof about
all arbitrary dictionaries. No native/extraction binding is silently inferred
from this selection. `SAQ_Forget.result` returns the original `Rc2_Result`
with exactly the same f/s/outer/pre/middle/fs/ss/run/tx2 witnesses, without
source hypotheses. The full elaborated before/after statements and axiom
lists are in [final audit](SAQ_107/stdout.log); sources are
[CompleteTop](../../lean/SAQ_CompleteTop.lean),
[CompleteInstall](../../lean/SAQ_CompleteInstall.lean),
[CompleteResult](../../lean/SAQ_CompleteResult.lean), and
[Forget](../../lean/SAQ_Forget.lean).

## Ledger correspondence

| Session A rows derived | Rc2 row IDs | Atomic P leaves |
|---|---|---:|
| Query basis/arithmetic/M31/decoder/line/line_canonical | N047–N088 | 42 |
| Geometry canonical | N089–N095 | 7 |
| Domain | N096–N104 | 9 |
| Explicit mul/one/inverse identities | N105–N107 | 3 |
| Total | N047–N107 | 61 |

Literal generic `Rc2_Top.deployed` delta: **0**. The source-selected candidate
recount is actual 82T+171P → 82T+110P; deduplicated actual plus non-alias
deployment 88T+184P → 88T+123P; all retained audit rows 88T+189P → 88T+128P.
Actual Session A 145 → 84; deduplicated actual/deployment 146 → 85.
No T or C row is removed or added; no replacement proof row is added.
[Recount script](SAQ_recount.py) reproduces [the reviewed row correspondence](SAQ_recount.json)
from the pinned Rc2 inventory; it is not itself a proof checker.
The authoritative ledger contains a separately labeled candidate append.

## Source proof and non-vacuity

M31 scalar and wide QM31 arithmetic uses retained extracted bodies and
finite-field lemmas, including unconditional raw-input successful-result
semantics/canonicality. Source line evaluation is split into channels and
Horner composition. The strict record parser uses its canonical existing
owner and proves the unchanged codec equation on actual successful parsing.
The extracted inverse loop/addition chain is equal as a Result to the retained
reference on every U32, including zero/error and noncanonical residues. The
source fibre constructor checks the actual 18-bit range; geometry uses the
retained source point/line bodies and derives domain/canonical obligations.

[Nonvacuity](../../lean/SAQ_Nonvacuity.lean) proves all three owner contracts
unconditionally for every input configuration/error value, accepts index 0,
rejects index 262144, and proves source inverse(1)=ok(1). It does not prove a
whole accepted native two-transaction execution. Optional zero-decoder rfl
fixtures failed and were excluded; the generic actual-parser theorem passed.

## Validation and frozen scope

All 100 actual Lean compiles (including dependencies) are retained, with 64
successes and 36 development failures; three preflight failures did not launch
Lean, and IDs 019–022 were unused. No more compiler attempts are authorized
under this budget. No Kani/Rust/SBF, package replay, memory kill or wall timeout.
Internal elaboration heartbeat/depth failures were split or replaced.
[Validation manifest](SAQ_validation.json) records counts and resource checks.

Final target `SAQ_Audit.lean`, attempt107: exit0, wall4.9601372859906405s,
peak RSS5308064KiB, swap0; source revision
33f52eda6f7dbc8d85a293119bd4bae6050052c4 plus pinned audit snapshot
(d46d91ac23380d3ccc0497717c98c87732896ee2f783bb360b42155c77760d50).
All accepted theorem audits use only propext, Classical.choice, Quot.sound.
Every compile reused the coherent host workspace from the requested HANDOFF,
in one admitted scope at a time: MemoryHigh6G/MemoryMax8G/MemorySwapMax0/
TasksMax64, Lean -j1 -M7000 -DElab.async=false. No cap increase. Exact
argv/target/tool/object/source hashes, status, wall, RSS, swap and axiom output
are in each attempt's receipt. Raw receipts are unmodified; stale copied
revision metadata is corrected explicitly by [source revisions](SAQ_source-revisions.json),
with exact source snapshots retained. [Selected closure](SAQ_selected-closure.json)
pins all 39 reachable prefixed modules against successful receipt snapshots.

Consumer092 found duplicate parser declaration owners; RecordDecode was
changed to the existing canonical owner and affected successors rebuilt95–100.
The three duplicate prefixed parser copies and failed combined LineMeaning
are archived as excluded text, absent from the selected Lean closure.
Session A files/worktrees and foreign modules were not changed.

[Source pins](SAQ_source-pins.json) retain protocol source hashes, base revision,
and inherited default/devnet/Pool ELF hashes. No shipped or cfg(kani) source
changed, so no ELF rebuild trigger. Pins were not freshly reproduced. Wire
format, features and protocol parameters were not changed. No key cleanup.

## Remaining blocker and next deliverable

Lead must integrate the source-selected dictionary and strengthened result
into the actual top before recording a generic Rc2 premise delta. Preserve
all existing native/extraction/P6/source-to-ELF boundaries (including L178),
retain SAP_'s SessionAPrepare ownership, and establish the selected error and
primitive dictionary's association to the actual deployment. The original Rc2
frozen2 headline is inherited unchanged; owner-approved frozen3 integration
is still required. RuntimePersistence remains an approved inherited runtime
trust item. No new trust item, release scope or cryptographic assumption was
introduced. Full S2 and the 100-bit release target remain unestablished.

## Stage commits

- f331b5ee2d Record Session A primitive baseline and source selection plan
- 0e90bbe802 Derive query scalar primitive laws at the selected Rc2 instance
- ef18bc359c Derive wide query arithmetic and compose the source-selected Rc2 top
- ade2d43103 Derive source geometry and inverse laws in the Rc2 continuation
- cb738de8f5 Derive unconditional source line laws at the selected Rc2 top
- 33f52eda6f Discharge complete primitive owners in the source-selected Rc2 theorem

Final evidence/audit commit follows these stages; no push.
