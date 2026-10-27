# Per-function fidelity check — SDY, 2026-10-27

**No premise removed, added, weakened or reclassified. No extraction repaired.**
S2 / A2 and the 100-bit release target remain open. This packet tests the four
D188-P3 suspended functions individually, rather than transferring the known
`low_base_p_digits` defect to them.

## Target and interpretation

Frozen native source: `4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`.
Raw Funs: `evidence/extraction-assoc2-20261027/XRj_L013/sources/XRj_generated/XRh_Release/Funs.lean`,
SHA256 `f4b2d17c061ce7062d64146531788b6448328e656fb6dbd6192f2d61db31a3b5`.
All emitted line numbers below refer to that exact file; Rust line numbers refer
to the frozen source, retained verbatim in `SDY_frozen_*.rs.txt`.

The raw file has no admitted unadapted executable environment (XRj_L013's
mutable-iterator/from_fn signature failures are retained prior evidence).
The requested executable comparison is therefore explicitly **on the XRn kit**,
rebuilt privately as `SDY_Join_*` against the coherent SInt2 cache. The 17-file
`SDY_kit_manifest.json` verifies exact inverse name/import replacement.
`SDY_body_diff.json` inventories every raw-to-XRn change in these functions
and their loops; it does not treat adapters as producer emission.

## Static write paths

| Function / frozen Rust write | Raw emitted write and restoration path | Static conclusion |
|---|---|---|
| `multiproof::verify_in_place`, multiproof.rs:177 `*child=value_at(...)` | Raw1193 obtains child1;1195–1197 passes `some(slot,child1)` through `next_back` then accumulated `back`. | Occupied child write retained. |
| Same, :182 `child.copy_from_slice(sibling)` | Raw1208–1214,1225–1231,1242–1248: `Array.to_slice_mut`, `copy_from_slice`, `to_slice_mut_back`, then `next_back(some(slot,child1))`, then `back`. | All three sibling-write branches retained. |
| Same, :189–190 `idx[w]=parent;val[w]=digest` | Eight-way1362–1364 restores enumerated iterator → mutable slice → child array,1365–1367 hashes that array,1368–1371 updates and returns idx/val. Binary paths1307–1311,1326–1330,1344–1348 likewise retain both Array.update outputs. Outer loop carries the arrays; function returns them on rejection too. | Child writes reach digest; idx/val writes reach returned state. |
| `verifier::update_residue_row`, verifier.rs:240 `row[j]=old+...` | Raw1935–1942 calculates i3, Array.update row j i3, returns row1 in loop state;1999–2005 consumes the completed loop. | Indexed writes retained. |
| Same, :243 `*limb=(*limb&...)+(*limb>>31)` | Raw1968 captures `next_back`;1973–1977 computes limb1 and composes `next_back im (some limb1)` with accumulated back. Exhaustion1970–1971 restores none. Caller2008–2012 obtains back and applies `into_iter_back back`. | Flush writes retained; raw ABI expects a restoration-function consumer here. |
| `sampler::add_small_base_p`, sampler.rs:93 `*digit=(sum%P) as u32`, :94 carry | Raw3484 captures `next_back`;3491–3498 computes sum, digit1, addend1;3499–3500 passes `some digit1` and carries addend1. Exhaustion3486–3487 retains composed back. Caller3523–3529 applies it through into_iter_back and returns the carry Boolean and digits. | Digit and carry writes retained. |
| `verifier::BatchedWeights::finish`, verifier.rs:226 `*w=self.value(i)` | Raw6364–6367 captures enumeration next_back;6372 discards only the **old weight**,6373 calculates new w,6374–6375 supplies `some(i,w)` to next_back. Exhaustion6369–6370 returns composed back. Caller6402–6408 restores enumerate → mutable iterator → slice. | New weights reach returned slice; old-value wildcard is not a lost callback. |

## Native and emitted fixtures

`SDY_R002` runs all twelve fixtures with `cargo test --release --locked --offline
-j4`, `CARGO_NET_OFFLINE=true`, in one 6G/8G/Swap0/Tasks64 scope. Every output
state is asserted, including unchanged tails. Native update/finish return unit;
the corresponding extracted Result carries their mutable output. No other
return value is omitted.

Let P=2147483647, `x×n` mean a repeated list, and `N(x)` the 32-byte node
`[x×32]`. For multiproof the explicitly selected fixture backend returns the
first byte of its first child, repeated 32 times. This observes restored child
writes and makes no claim about a cryptographic hash implementation.

| Function / fixture | Exact native input | Native output / proved complete kit Result |
|---|---|---|
| add A | digits `[0×8]`, addend1 | `ok(false,[1,0,0,0,0,0,0,0])` |
| add B | digits `[(P−1)×8]`, addend1 | `ok(true,[0×8])` |
| add C | digits `[5×8]`, addend P | `ok(false,[5,6,5,5,5,5,5,5])` |
| row A | row[1,2,3,4], power(1,2,3,4), basis2, flush=false | `ok([3,6,9,12])` |
| row B | row[2147483648,2147483649,4294967296,7], power0, basis0, flush=true | `ok([1,2,2,7])` |
| row C | row[P,0,0,0], power(1,2,3,4), basis1, flush=true | `ok([1,2,3,4])` |
| finish A | raw[[1,2,3,4]], terms0, weights[(99,99,99,99)] | `ok([(1,2,3,4)])` |
| finish B | raw[[2147483648,2147483649,4294967296,7]], same terms/weights | `ok([(1,2,2,7)])` |
| finish C | raw[[P,4294967294,0,2147483652]], same terms/weights | `ok([(0,0,0,5)])` |
| multiproof A | Eight, rootN(0), idx[8,0×15], val[N(5),N(0)×15], n1, nodes[2×224] | `ok(false,[1,0×15],[N(5),N(0)×15])` |
| multiproof B | same, idx[9,0×15], val[N(7),N(0)×15], nodes[3×224] | `ok(false,[1,0×15],[N(3),N(0)×15])` |
| multiproof C | same, idx[10,0×15], val[N(9),N(0)×15], nodes[4×224] | `ok(false,[1,0×15],[N(4),N(0)×15])` |

Multiproof completes one eight-way level and rejects when its next level lacks
a sibling. Its full output arrays therefore test writes before rejection;
checking false alone would miss the relevant state. The three child positions
exercise both occupied-child assignment and sibling slice copy.

Every Result in the table is proved by the complete-function theorem listed
below, and matches the native state and return. There is no pending fixture.

## Verdicts and proof receipts

| Function | Verdict | Complete Result theorems / passing receipts |
|---|---|---|
| `sampler::add_small_base_p` | **FAITHFUL on the fixtures** | `SDY_AddA.emitted` L019; `SDY_AddB.emitted` L020; `SDY_AddC.emitted` L030 (symbolic step predecessor L029). |
| `verifier::update_residue_row` | **FAITHFUL on the fixtures** | `SDY_RowA.emitted` L026; `SDY_RowB.emitted` L031; `SDY_RowC.emitted` L032. |
| `verifier::BatchedWeights::finish` | **FAITHFUL on the fixtures** | `SDY_FinishA.emitted` L035; `SDY_FinishB.emitted` L036; `SDY_FinishC.emitted` L037. |
| `multiproof::verify_in_place` | **FAITHFUL on the fixtures** | `SDY_MpA.emitted` L059; `SDY_MpB.emitted` and `SDY_MpC.emitted` L060, both in `SDY_MpBC.lean`. Child-step predecessors L046–L048. |

All twelve final prints are exactly the standard axiom set
`[propext, Classical.choice, Quot.sound]`. Every new helper theorem also has a
print in its compilation log. `SDY_AXIOMS.json` selects the twelve final
prints and their passing receipts; failed-run prints containing `sorryAx` or
the rejected `run0` placeholder are **excluded**, never accepted as proof.

The proof uses separately established loop steps and finite compositions.
The symbolic `SDY_Loop.range` handles platform-sized iterator bounds;
`SDY_AddC.step_eq` prevents kernel conversion from unfolding large carry
arithmetic; `SDY_Slice.read` proves repeated-byte slice reads by list shape
before any concrete call. No whole-function loop was normalized, no new axiom
or heartbeat/recursion-depth limit was introduced, and no emitted body was
edited beyond the kit's exact name/import copying.

## Emission and adapters are distinct

`SDY_body_diff.json` verifies the only raw-to-XRn substitutions in the checked
write paths:

- Both enumeration-next consumers use `XRn_Join_enumerateNext` (ABI:5–13), which
  obtains the pinned forward `IteratorIterMut.next` callback and supplies the
  new item's second projection to it. That std callback writes `setAtNat` at
  its captured original index (retained std SliceIter:39–52).
- Array-mutable `into_iter` in row/add uses `XRn_Join_intoIter` (ABI:25–28).
  It consumes the accumulated restoration **function**, applies it to the
  initial full iterator, and recovers the array from its slice.
- Finish's enumeration restoration uses `XRn_Join_enumerateRestored`
  (ABI:44–48): it applies the accumulated function to the original enumeration
  and projects the resulting iterator. Multiproof's inner loop instead returns
  its fully restored enumeration directly; it uses the plain enumeration
  projection (StdExtra:19–24), followed by the slice and array restorations.

These forward restorations set existing indices and preserve the slice length;
the complete fixture Results show no fallback to an old array and no adapter
change to the observable native result. They do not use the append-back reverse
adapter implicated in SDX. **No adapter-caused result discrepancy was observed
on these fixtures.** This is not a universal ABI-equivalence proof, nor an
adoption of worker externals under D188 or P7. In particular, the raw unadapted
file's signature/elaboration obstruction remains separate from these executable
kit comparisons. Field/library models and caller validity still require their
existing association obligations.

## Whole-file discarded-restoration grep

`SDY_static.py` scans the whole raw Funs, including multiline tuple bindings,
retains every wildcard tuple binding in `SDY_scan.json`, then classifies the
wildcard position against the mutable accessor's return. The complete hit list
for **a discarded mutable back-function**, rather than an ignored old value,
readonly iterator state, or closure, is:

| Raw line | Shipped function / emitted declaration | Binding and consequence |
|---|---|---|
| **3611** | sampler.rs:61–65, `sampler::low_base_p_digits`, `sampler.low_base_p_digits.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut_loop.body` (declaration3599) | `let (o, iter1, next_back, _)` from mutable reverse-next discards field4, the mutable restoration callback. The quotient is separately discarded at3624. Rust sampler.rs:63 writes it through `*limb`. |

There are **no further hits** in this raw Funs. The unused first component of
`(_,index_mut_back)` retains its back-function; finish's `(i,_)` discards the
old weight and supplies its new weight at6374. Neither is this pattern.
The fresh line audit corrects SDX's prose shorthand: **3611 is the binding;
3624 is the discarded division result**. The raw source hash is unchanged.
This is a scan of emitted bodies only; opaque native leaves have no body here
to scan and are not covered by a completeness claim.

## Exact consequence for D188

The known sampler dropped-write finding is **not reproduced in these four
functions**. Their written values reach the kit's returned state, and the
three complete Result fixtures per function agree with frozen Rust. The four
rows can be reported as FAITHFUL **on these fixtures** rather than collectively
labelled UNFAITHFUL because of the shared iterator family.

This packet **does not establish general D188 trace fidelity**, remove a
premise, or authorize lifting a universal suspension by extrapolating fixtures.
The owner's D188 contract covers arbitrary associated inputs and chronological
attempted digest calls, including duplicates/rejected prefixes; this packet has
no general such trace theorem. Raw elaboration, universal adapter association,
adopted-cohort association and source-to-ELF obligations remain. D188 credit
for `low_base_p_digits` remains excluded by D188-P3. Existing cohort theorems
remain theorems about their pinned cohort. No shipped Rust/ELF defect, root
invalidity, new trust item or changed security metric is claimed.

## Verification, resource receipts and handoff

Budget consumed: **60/60 Lean attempt slots** (59 compiler launches and one
missing-dependency preflight), **2/15 Rust runs**, **0 Kani**. No further prover
run was launched after slot60. Compiler runs:36 pass,23 fail/stop; all failed
receipts are retained and excluded from final proof credit. The early dependency
ordering failure L003 has no compiler timing/RSS/axioms and is explicitly marked
not measured in `SDY_L003_preflight.json`; it did not bypass admission.

Each compiler receipt records exact target/argv, source revision and SHA256,
selected dependency objects/sidecars, exit, wall time, peak RSS, swaps, full
printed axioms/errors and checked scope limits. All scopes were
MemoryHigh=6G / MemoryMax=8G / MemorySwapMax=0 / TasksMax=64, Lean -M7000.
Admission required reservation JSON `allowed:true` **and** script exit0;
the committed invocation code enforces both before copying compiler inputs.
No admission refusals/retries occurred. Only one owned capped scope ran at a
time; no other worker's job was stopped or modified.

| Final target | Exit | Wall seconds | Peak RSS KiB | Swap | Source revision (dirty, exact sources pinned in receipt) |
|---|---:|---:|---:|---:|---|
| SDY_L059 / SDY_MpA | 0 | 3.537470696028322 | 2698308 | 0 | 9cc3a59f794bf31be2119f53c14d5e60f7bb6b3e |
| SDY_L060 / SDY_MpBC | 0 | 5.346750786993653 | 2712672 | 0 | same |
| SDY_R002 / twelve native fixtures | 0 | 1.9734432370169088 | 233416 | 0 | fc7ae2a2ba9faef4adb0f9920786a63fde53f6fb |

The Lean compiler aggregate wall time was 223.2427195800119 seconds; peak
7168740 KiB; all swaps 0. The peak is **failed** L025's kernel memory-limit
rejection, not an accepted theorem. `SDY_resource_replacement.json` records its
cause and replacement. L028's preliminary split was manually stopped after
excessive growth. Neither was rerun unchanged or with a raised cap. The eventual
L029/L030 symbolic-step split passes in 2.4556471050018445 / 1.4372487859800458
seconds respectively. Other failed attempts concern bounds, checked additions,
concrete slice reduction, constructor typing and shared-iterator loop association;
the final bodies use symbolic slice/range facts and explicit finite loop steps.
There was no timed-out run. R001's missing test-local std import is corrected
in R002. No failure is presented as evidence that the corresponding theorem
is false.

Native source validation additionally checks **538 Rust/manifest files** in the
scratch source overlay against frozen git blob identities, treating the three
cfg(test) appendices explicitly (`SDY_frozen_tree_check.json`: zero mismatches).
The frozen lock SHA256 before/after each native run is
`5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef`;
resolved package tuples were validated before each run. Graph/lock records and
both failed/successful wrapper snapshots are retained. Unchanged source files
were accessed through symlinks; only the owned three source overlays and lock
were written. No second full source corpus was copied. The inherited compiled cache was reused read-only.

Reused: the coherent SInt2 objects and source/object manifests, pinned XRn kit,
raw extraction/producer provenance and prior raw elaboration failure. Newly
checked: 17 private kit modules, symbolic helpers, all twelve complete fixture
Results, frozen-source/lock/graph checks and the whole-file wildcard scan.
`SDY_AXIOMS.json` is a selection audit of the final passing prints; an extra
aggregate Lean audit module was not run after the budget was exhausted.
`SDY_Audit.lean.candidate.txt` and standalone B/C tail candidate text are
unexecuted planning artifacts; **L060's SDY_MpBC is the compiled B/C owner**.
The initial fixture-writing scripts and edits are retained as working history;
the final source snapshots and accepted receipt hashes are authoritative.

`SDY_VERIFICATION.json` / `SDY_attempts.jsonl` audit final source hashes, accepted
axioms, limits, admissions, kit inverse equality and scope. Build outputs owned
by this job were hashed and removed: 96 files, 83936001 bytes
(`SDY_cleanup.json`); source and receipts retained. Keys and wallets were
untouched. All changes are under `evidence/fidelity-check1-20261027/` and all
modules use SDY_. Session A worktrees/candidates were untouched. Commits are
local; no push or merge.

No shipped file or cfg(kani) harness changed, so no SBF rebuild was triggered.
The three ELF pins are **inherited, not freshly reproduced**:

- default `f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4`
- devnet `63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299`
- Pool `121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548`

No whole frozen manifest, adversarial/runtime suite or root replay was run;
this is a focused diagnostic with no changed shipped artifact. The remaining
lead deliverable is an owner-scoped decision on general D188 fidelity and
adapter/cohort association, while separately resolving the confirmed
`low_base_p_digits` missing write. This packet repairs neither. The 100-bit
release target remains **not established**.
