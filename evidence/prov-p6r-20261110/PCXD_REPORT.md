# PCXD_ report: provenance, P6 refresh (final recount before the owner's decisions)

Scope. Provenance only, over the evidence on research at c933144b87e (P2i, P2j, P3b, P3e, P6x) with the PCXB_ method. Ledger30 gate (base 6ce07a6a593), frozen source 4bb3b3f. No ledger row, trust row, RSL, security contract or shipped source changed; no trust row added. Out of scope and not covered: the release replay, L187/L188 (only the source reconciliation is repeated), R22 (it owns checked-versus-wrapping; its pin b2727acd is not 4bb3b3f) and source-to-ELF.

## 1. Headline: AspisR1.TAS_FinalB.deployed_splitB

The cone has 146370 constants (pinned list, hash verified, reach step rerun with identical module hits). It reaches 209 of 373 emitted gate modules and 1707 definitions that carry a status:

* EQUALITY_PROVED 848; RECEIPTED 256; EQUALITY_DOMAIN 6; CONDITIONAL_ON_BINDING 6; HAND_ADAPTED 33; NO_FROZEN_COUNTERPART 4; OPEN 554.
* OPEN splits into 325 with no overflow-correct fresh emission, 172 failed or other, 40 with no record, and 17 wrong-basis (counted OPEN).
* Module rollups: 133 OPEN, 40 RECEIPTED, 26 EQUALITY_PROVED, 1 CONDITIONAL, 9 reach no annotated definition.

Inside the 848: 691 are on an overflow-ON emission, 74 OFF, 2 OFF-default, and 81 are Types records with no arithmetic configuration; 61 of the 848 are Equiv isomorphisms of Types declarations (constructor-wise or structure-wise), not term equalities. Nine are OFF by the wrapping ruling (section 3), 2 more are OFF because their gate declaration itself uses wrapping_*, and 35 rest on the ShrAmt bridge, verified by NPE_ for overflow-checks-off only (2 more EQUALITY_DOMAIN definitions do too). RECEIPTED means a hash-linked extraction receipt whose overflow configuration is not re-derived here.

The 599-row ledger30 view, recomputed from committed tables (PCXD_ROW_TABLES.json): 163 clean at definition level (138 in PCXB_), 422 conditional, 12 reach no emitted module, 2 rootless. "Clean" is over annotated names only; hand-written names and the hand models are outside it, and 561 rows still rely on a module whose rollup is OPEN. Method, so a stranger can rerun it: each of the 1099 ledger roots has a pinned reachable-constant list; intersecting it with each emitted module's owned names (PCO partition rule) gives root-to-module-to-names; inverting through roots-to-rows gives row-to-module-to-definition; a row is clean if it reaches at least one emitted module and every annotated definition it reaches is RECEIPTED, EQUALITY_PROVED or EQUALITY_DOMAIN. The reach step and the first table reproduced the PCXB_ tables byte for byte.

## 2. Delta from PCXB_

| quantity | PCXB_ | PCXD_ | why |
|---|---|---|---|
| EQUALITY_PROVED (cone defs) | 694 | 848 | +154: P2i wrong-basis and Types re-proofs and P2j ON moves, P2j TerminalDecoder second shapes and LOGICAL_Y1, 3 P3b V8R19 M31.mul (split by basis below) |
| OPEN (cone defs) | 708 | 554 | the same 154 moved |
| WRONG_BASIS open | 119 | 17 | P2i re-proofs on a correct basis |
| FAILED_OR_OTHER open | 224 | 172 | 52 fewer |
| module rollups OPEN / EQUALITY_PROVED | 143 / 16 | 133 / 26 | ten modules completed |
| clean rows / conditional rows | 138 / 447 | 163 / 422 | same row rule |
| combined import | 13 bundles, 200 files, 2121 theorems | 17 bundles, 251 files, 2472 theorems | 4 new bundles; no native.decide axiom |
| non-frozen cone modules, definitions | 170 EQ, 150 OPEN | 231 EQ, 89 OPEN | statuses refreshed |
| hand models, externals (a/b/c) | 245; 502/0/99 | 245; 502/0/99 | no hand model added |

Nothing moved from proved to open. The 154 moves are all OPEN to EQUALITY_PROVED, by basis: 124 ON-emission, 10 clean O1 recompile, 9 OFF wrapping-closure, 6 second-shape, 3 P3b, 2 OFF wrapping-declaration.

## 3. Corrections applied (brief items 1 to 6)

1. P2j listed M31.mul in AspisV8R19 Complex and Guarded as open. P3b proved fresh = gate as functions with no hypotheses for Complex, Guarded and Quartic (PCVB_L041-L043). The files name the same fresh emission (sha256 3fe20d13 and 04b39d85) and the same gate constants as the P2f records, so all three are credited (classification PCXD-C2); the AspisR72Sampler credit was already in place.
2. The nine NNG/NJS wrapping-closure definitions are EQUALITY_PROVED with configuration OFF recorded and are counted as their own class.
3. Of the original 29 CONFIG_INDEPENDENT_BY_TEXT_OFF_EMISSION_ONLY: 20 are proved at ON, 9 are the closure set. No residual class remains.
4. The 10 PCUI_L029 theorems are credited only through PRVEq_O1clean.lean (PCUJ_L002).
5. Transport: row EQUALITY_PROVED; row_loop.body and row_loop EQUALITY_DOMAIN for end <= 16 (the bound is a hand argument for sharpness); ShrAmt verified for OFF only.
6. Equiv Types records are flagged as isomorphisms; constant-binding and parametric-transport results stay CONDITIONAL_ON_BINDING (6); wrong-basis stays OPEN.

One defect found and fixed in my own tooling: PCUI/PCUJ records carry a stale proving_file basename pointing at the superseded P5 file, which first credited 17 wrong-basis files; credit is now by theorem name inside the deciding phase directory (PCXD-C3).

## 4. Combined import and audit

PRVCmb_ROOT imports PRVH_WrapAdd and bundles C01..C17. C01..C12 are the PCXB_ objects and C13 the PCXC_ corrected object (pinned by sha256 in the root receipt); I compiled C14..C17 (the 51 new files) and the root. All five scopes exit 0; the longest took 39 s, peak 6.2 GiB at the root, swap 0, caps unraised. The root audit covers 3340 constants under PRV*/PCVE*/PCVB*: all 2472 theorems audited one by one, each depending only on propext, Classical.choice and Quot.sound; the union of axioms is those three; no local axiom declarations. All 920 credited theorem records are found by name (renames in PCXD_RENAMES.json; PCXD-C4 adds the PCVB_ helper namespaces to the rename rule). Generator-set maxHeartbeats of 400000 on three P3b theorems are below the Aeneas default of 1000000 and are recorded. Excluded: 361 PRVEq files that prove only superseded, wrong-basis or open records, and all scratch with sorry.

## 5. What is proved, conditional, open

Proved: the 848 + 6 equalities above, in one environment, on the stated bases. Conditional: the 6 constant-binding or parametric-transport results; the 256 RECEIPTED on their receipts; everything resting on the ShrAmt residuals (no SBF-target check; shared Lean usize width) and on the 245 hand-written gate models; every checked-configuration definition on R22 (by body class: 51 wrapping, 217 checked, 8 checked with some wrapping, 1431 without arithmetic; the shift case is listed once as mixed configuration inside one body). The equalities tie reproduced text to the gate, not archived crates to the frozen source, for the 24 no-source and 26 second-tier cut modules. Non-frozen: 26 cone modules, 4 fully proved, 21 unverified (detector-blind), 1 open; all 8 gate-only definitions are reachable from the headline at constant level (not semantic use); NJT_claims_ref is a hash-linked reference, not an orphan. Open: 554 definitions, 33 HAND_ADAPTED, 4 NO_FROZEN_COUNTERPART, 20 of the 24 no-source modules, and at most 99 unresolved externals.

The 23 FAILED records P2j did not attempt stay OPEN (PCXD_NOT_ATTEMPTED_23.json): four WideToBytes functions (three in WideToBytesSource, one in the Indexed candidate; gate written against P6ToBytes.StdModel iterators, the emission uses ChunksExactMut); fifteen whose P2d/P2f/P2h/P2r generator inputs the PCUI_ tooling does not carry (NJA node_count, NMT digest/data/stage1_owned, Port23PUSH push, heap.filled, Dot.push, five FIp four_dots functions, three S1NativeCompact expand_semantic functions); decode_pool_v1_pair_verified_afterstate_v1 (the recorded emission already includes the transparent P); secure_ood_circle_point_from_parameter (heartbeat timeout in two shapes); mul_by_r (waiting on a non-frozen extraction); Option.ok_or (unsolved goals). Reason in each case: no distinct shape or input was available to P2j, not a finding that the equality is false.

## 6. Files

PCXD_PROVENANCE.json, PCXD_ROW_TABLES.json, PCXD_R22_SPLIT.json, PCXD_HAND_MODELS.json, PCXD_EXTERNALS.json, PCXD_NONFROZEN.json/.md, PCXD_NOSOURCE.json/.md, PCXD_L187_RECONCILE.json, PCXD_TRUST_PROPOSALS.md, PCXD_STATUS_LINE.md, PCXD_OWNER_DECISIONS.md, PCXD_AUDIT.json, PCXD_DELTA.json, PCXD_SUPERSEDED.json, PCXD_CLASSIFICATIONS.json, PCXD_TOOLS.json, PCXD_ATTEMPTS.jsonl, PCXD_HANDOFF.md.

Target not yet established.
