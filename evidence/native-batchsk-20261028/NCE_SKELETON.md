# NCE skeleton audit

Stage 1 is NOT complete. No end-to-end native bridge is claimed.

## Target and interpretation requiring resolution

The requested exact accept/first-error result must distinguish an exact Rust
`Result` from the adopted acceptance/rejected-prefix observation. They are
not interchangeable. Frozen Rust `candidate.rs:198-204` returns `Err(Parse)`
on capacity/padding failure, and `Err(Merkle)` on failed verification. The
retained `Port3_NativeBatchBody` terminal body produces `done (...,none)`
and its enclosing `batch_tree` converts `none` to `fail panic`.

This is an existing, recorded extraction discrepancy, not a newly discovered
implementation defect. C3-BIN “L166 finding and ruling; D188 fidelity note”
adopts success-conditioned correspondence with every rejected digest prefix
counted. It explicitly does not require equality of error kinds.

`Port4B_Rejection.padding_result_differs` proves the local exact-return
inequality. Checked `NCE_ErrorObstruction.exact_error_obstruction` consumes that
existing theorem on arbitrary SAME idx/val, and
`exact_error_and_prefix_obstruction` retains ANY chronological prefix.
Neither assumes acceptance nor changes an error into success.

A theorem asserting exact source/cohort Result equality on this branch
cannot have simultaneously faithful, satisfiable per-step native hypotheses.
Calling that hypothesis `NCE_Native_Padding` or `NCE_Native_ThreeTrees`
would hide a false conclusion. No such hypothesis has been introduced.

## Eight native interfaces to audit

These are concrete remaining interfaces, NOT Lean declarations or discharged
facts. The following list is deliberately not presented as a compiled skeleton.
Every proposed interface quantifies over one arbitrary reached prestate of
the same immutable Prepared/proof and mutable scratch, cursor and chronological
log. No final count, final padding scan, accepted tree or final log is an input.

1. **NCE_Native_Count**: one count microstep, selected by its source PC:
   initialization window, equal-parent scan test/advance, row accumulator and
   parent store, or height transition. Exact scalar poststate and arbitrary
   coordinate frame. Associate these PCs to `NBI_CountScan.scan`,
   `NBJ_CountRows.nativeRows`, and `NBY_CountCarry.carry`; initialization uses
   `NBV_CountInitialization`. A single row does not establish its own inner
   scan. Harness: one PC on symbolic level[16], cursor/count/height and one
   arbitrary observed coordinate. No whole eighteen-level invocation.
2. **NCE_Native_Row**: one binary node request/reply and write window:
   paired versus supplied/short, exact request component pointers/bytes,
   unchanged returned reply, cursor/i/w transitions, one index store and
   selected byte write, all exterior coordinates framed. Consumers:
   `NBJ_NodeObservation`, `NBY_RowCopy`, `NBY_RowCarrier`, `NBI_Frame`.
   Harness: arbitrary scratch, symbolic i/w/at and offset, one byte/window;
   symbolic runtime reply, no SHA. Compose byte windows only on the SAME reply.
3. **NCE_Native_Verifier**: source PC for entry admission, exhausted-row n=w,
   height increment or final n/index/root/cursor guard. Exact control/result,
   scratch and log frame. The row transition uses item 2, not an opaque open
   verifier stub. Consumer: `MultiproofConePhysicalLevels` and existing
   node/level inductions. Harness: one selected control cut on arbitrary
   prestate; never all levels.
4. **NCE_Native_Opening**: one selected proof-byte read/reborrow at absolute
   `10055+832*i+32*w+c`, with i<22,w<26,c<32, fixed SAME backing pointer,
   and unchanged exterior. Consumers: `NBY_OpeningLocality.opening_loads`,
   `NBJ_Address`, `NBV_WindowFrame`. Harness: one byte/window on arbitrary
   backing, not 22 enumerated positions or an entire proof equality.
5. **NCE_Native_Keys**: source PC for zero initialization, raw query read,
   packed-word store, insertion-sort comparison/move or iterator return;
   exact selected word and unchanged exterior. Canonical query provenance
   comes from the named NBR_/NBS_ lower dependency, not a new headline law.
   Consumers: `NBE_KeyLoop`, `NBI_Keys`, `NBI_Sort`, `NBJ_Keys`.
   Harness: one PC on arbitrary key/query arrays, symbolic cursor/coordinate.
6. **NCE_Native_Leaf**: one key iteration, with exact selected opening and
   one leaf digest request BEFORE duplicate test, exact returned digest,
   duplicate/new/error control and selected idx/val write frame. C1/C2/folded
   request components use actual source tag/value/salt slices. Consumers:
   `Port4B_NativeLeaf`, `Port4B_LeafStep`, existing leaf fold inductions.
   Harness: one request or post-return window on arbitrary SAME prestate;
   no assumed successful selected opening or duplicate continuation.
7. **NCE_Native_Padding**: one physical 8-byte chunk predicate/iterator step
   with exact first-stop continuation and unchanged scratch/log. Bind its
   partition to the SAME count and nodes from preceding steps. Consumers:
   `NBJ_PaddingPort.physical_scan`, `NBI_Padding.first_stop`.
   Harness: symbolic chunk/iterator prestate; no final successful scan.
   **Exact error equality is obstructed at its caller return**, as above.
8. **NCE_Native_ThreeTrees**: one source outer control step dispatching tree
   0/1/2 or returning at the first failed child; next tree consumes the
   preceding scratch and log; SAME Prepared, proof, query/root projections.
   Entry/exit uses actual TX1 or U09 return carrier and named NBR_/NBS_/U00
   lower dependencies. Harness: one dispatch/return PC, not successful
   independent tree calls. `Port3_NativeBatchCalls.values_calls` is only an
   accepted-path inversion; `Port4B_BatchJoin.compose` assumes three model
   successes and cannot itself supply this native association.

## Composition audit

The inherited NB*/Port4B results are mathematical/value or installed owned
model results. `Port4B_StageRows.tx1/tx2` have explicit installed-operation,
Prepared provenance, P6 and accepted-run boundaries; their statements do not
establish these eight native interfaces. Merely importing them cannot prove
exact arbitrary-error native execution correspondence. No XRn_Join kit,
arbitrary whole-child stub or substituted headline is used here.

## Capacity-recovery continuation

The L166 ruling already resolves the observation: successful values and ordered
rejected prefixes are retained; exact error-enum identity is not required.
The previous pending interpretation question is therefore not a stage gate.
The exact-error obstruction above remains valid at its stronger observation.

`NCE_FirstFailure` now constructs the first failed TREE observation from the
existing cohort's actual evaluations, carrying each prior return into its next
child. `sequence_observation` identifies its log, success Boolean and final
scratch with the existing sequence on EVERY outcome. `batch_observation`
instantiates exactly three chronological children for arbitrary batch and
initial scratch. `stop_here` retains the rejecting child's reads and leaves
an arbitrary suffix unvisited. This is the model/control part of the requested
skeleton; it supplies NONE of the eight native associations. Stage 1 remains
incomplete. No new native interpreter or execution-join stand-in was added.

L004 passed: source, dependency/Aeneas pins, scoped resource fields and all
five standard-only axiom reports are in `NCE_L004/receipt.json`. Budget after
recovery: 4/60 Lean, 0/70 Kani (also within the earlier 120/50 ceiling).

### Typed count scan fragment (L009)

`NCE_CountCuts.NCE_Native_CountScan native` is a separately named, prospective
ONE-test/advance hypothesis. It is NOT the entire item-1 `NCE_Native_Count`.
On `ScanDomain s` it requires the source predicate, cursor update, pointwise
unchanged keys, unchanged n/parent and unchanged arbitrary caller frame.
Domain: cursor<=n<=16, parent<262144 and each live key<262144.
`entry_domain` derives that domain with parent=key[i]/2 from the admitted
live-key range; `initialized_entry_domain` consumes NBV's existing copied
prefix. `scan_step_domain` preserves it. `scan_run_eq` composes the cut along
its actual returned state and identifies the inherited NBI scan recurrence.
`scan_run_group` consumes NBI's existing group theorem, including width1/2.
No count accumulator, count result, success or log equality is assumed.
A native harness would execute one inner while-test/advance on arbitrary
level/cursor/parent, select one arbitrary exterior coordinate and frame the
remaining caller state. Actual Rust/P6 association remains OPEN.

L005-L007 failed, retained and excluded. L008 checked the four initial roots;
L009 checks the final renamed interface plus two entry-domain roots. All six
L009 roots use standard axioms only. See NCE_REPAIRS.md and per-attempt receipts.

### All-outcome cohort composition (L010)

`NCE_CohortObservation.three_trees` consumes the existing P6 local gates and
physical slot bounds to identify the first-failure observation of ALL three
trees with that of the existing owned slot model. No successful-tree premise
is introduced; the current poststate is always the next tree's prestate.
`batch_result` identifies the cohort batch's entire chronological log and
Boolean with that SAME owned first-failure observation. Batch b is arbitrary
with b<2, covering TX1 b=0 and TX2 b=1. These model results do not instantiate
native keys/count/padding, actual control lowering, Prepared provenance or U00.
L010 passes; all three roots standard-only. The requested native skeleton
still needs those bindings, so Stage 1 is NOT complete.

### Typed post-scan count commit and row association (L014)

`NCE_CountRowCuts.NCE_Native_CountCommit` is one post-scan accumulator/index
store, quantified over arbitrary key coordinates and caller frame. Its exact
poststate is key[w]=key[i]/2, unchanged other keys/n/frame, i=j, w=w+1 and
count=count+(2-(j-i)). Domain: n<=16,w<=i<j<=n,j-i<=2,count+2<2^64,
all live keys<262144. `commit_eq` reconstructs that single source write from
its coordinate/scalar laws. `rows_port` consumes this cut plus the separately
named scan cut on each actual predecessor. NBI supplies the endpoint/width;
NBY supplies the overflow domain and next spent bound. It derives the NBJ row
result and unchanged caller frame, with no final-row/count premise.
Native initialization, outer count/height control, admission and concrete
same-caller Frame instantiation remain open; this is not the full item1 gate.
L013 failed/excluded; L014 passes, both roots standard-only.

### Shared actual carrier and byte reader (L015)

`NCE_OpeningRead` defines `NCE_OpeningCuts.Carrier`: the actual VTop Prepared,
proof Slice, reference scratch and chronological log. `NCE_Native_Opening`
requires ONE selected byte/reborrow at10055+832*i+32*w+c to return that same
proof backing's byte and unchanged full carrier, on i<22,w<26,c<32 and frozen
proof length57607. `read_byte` derives every linear opening offset via the
existing window coordinate arithmetic. Native harness: one selected load on
actual proof/reborrow pointer, arbitrary symbolic selected indices and
arbitrary exterior coordinate; no whole-proof equality or zero surroundings.
L015 passes. The complete opening continuation remains a separate target.

### Opening, keys, sort, row store, leaf and padding cut consumers

All following hypotheses are prospective P6 native cuts, NOT native passes.
They have no sorry/axiom declarations. These typed fragments do not yet form
the requested single eight-hypothesis same-execution top theorem.

- L020 `NCE_OpeningCuts.opening`: sequential byte reads consume their actual
  predecessor's returned Carrier and reconstruct the whole selected opening
  image with unchanged full caller. It uses the one-byte L015 cut. No native
  whole832-byte or full-proof run is required.
- L030 `NCE_KeyCuts.NCE_Native_KeysWrite`: one raw query read/packed U64 write
  at arbitrary cursor; selected value is the natural256*index+position,
  every other key and Prepared/proof/scratch/log is unchanged. Domain is
  batch<2,kind<3,cursor<10/12,canonical physical queries. Existing NBI packing
  identifies that raw value with the model; fill_eq/fill_values consume the
  inherited NBE recurrence along actual poststates. Query canonicality needs
  the named NBR_/NBS_ caller bridge; native zero allocation remains separate.
- L022 `NCE_SortCuts.NCE_Native_KeysSort`: one compare/swap/stop at cursor<16
  on arbitrary16 keys. Its postcondition is NBI_Sort.NativeStep, including the
  swapped values, decreasing cursor and outside frame. Existing step_port is
  reused. Native insertion/full-sort continuations equal the emitted model
  by induction; no sorted-array result is an input. Separate source control/
  allocation/iterator associations remain.
- L033 `NCE_RowStoreCuts.NCE_Native_RowStore`: one post-hash index write plus
  one selected32-byte digest window on arbitrary SAME Carrier and arbitrary
  actual reply. Domain w<16. Each arbitrary j<16,c<32 obeys the selected-byte/
  outside law, idx[w]=parent and all other idx coordinates are retained;
  n/prepared/proof/log stay fixed and at becomes the supplied actual cursor.
  store_eq consumes NBI's array frame; stored_bytes consumes NBY's KMX law.
  Native request selection/reply/source assignment association is still open.
- L025 `NCE_LeafCuts.NCE_Native_Leaf`: phase-selected one request/reply or one
  post-hash control step. Request domain kind<3/view.length832; it retains ANY
  raw prefix and exact source component slices/reply, paired with the existing
  Port4B_LeafCode theorem under the runtime digest law. Post domain scratch.n<16;
  it retains duplicate-success, duplicate-error and insertion control and full
  caller frame via existing Port4B_LeafStep.post_exact. The SAME actual returned
  digest is passed to post. Raw/high-level log transport and selected native
  opening association are explicit remaining joins, not hidden assumptions.
- L026 `NCE_PaddingCuts.NCE_Native_Padding`: one extracted iterator/predicate
  iteration on arbitrary physical chunks and arbitrary Frame, all reached
  chunks length8. It includes exact stop/continue and unvisited iterator state,
  preserving Frame. run_eq consumes NBI's existing scan; first_stop consumes
  NBI's existing first-stop theorem. No final successful scan is a hypothesis.
  Native physical partition/count association and exact predicate lowering
  still require concrete instances.
- L032 `NCE_CountLevelCuts.NCE_Native_CountHeight`: one outer n=w/height+1
  transition, unchanged returned private key/count/caller frame. Domains
  w<=16/currentdepth<18 are derived from the actual preceding row result.
  level_port consumes checked scan+commit cuts and NBJ/NBY count results to
  derive the next live keys, count, order/range/size and spent invariant.

Source paths are under docs/research/100bit-spend-path-20261013/lean/.
All listed final roots pass with standard axioms only. No frozen replay,
Rust/Kani/SBF gate or native premise removal is claimed.
