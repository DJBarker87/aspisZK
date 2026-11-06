# NLF SDK borrow support laws

Target not yet established. These are reusable **std-interpretation support
laws under (be)(2)/(au)**, paired with native checks of pinned wrapper logic.
They are not ledger rows, a native entry-driver packet, or a security theorem.
Baseline ledger20 remains 560 CLOSED / 0 QUALIFIED / 39 OPEN of 599.

`import NLF_SdkBorrowLaw` loads the following statements. All new top theorems
have individual `#print axioms` receipts; combined raw audit is recorded in
NLF_AUDIT.json. Universal statements below retain the SAME State, account index,
cell, token, payload and result; no free operation dictionary appears.

| Required member | Exact statement / domain | Consumers |
|---|---|---|
| Shared SDK data borrow | NLF_SharedDataLaw.result: for every s,a,t with ghost freshness t not in the selected cell's readers, try_borrow_data returns the SAME data-cell guard and readers=t::oldReaders iff 0 <= flag < 2^63-1; otherwise unchanged state and AccountBorrowFailed. NLF_ParentModel.fresh derives freshness from Below, and shared_preserves proves the complete global invariant after either arm. | TX1:344/345 snapshots; TX2:241/233 snapshots/authentication; Pool guard owners |
| Exclusive SDK data borrow | NLF_ExclusiveDataLaw.result: for every s,a,t, try_borrow_mut_data succeeds iff the selected cell flag is zero, changing only its writer to some t; otherwise unchanged state and exact AccountBorrowFailed. exclusive_preserves maintains global validity and token uniqueness. | TX1:344 checkpoint write; Pool mutable guards |
| Ref / RefMut deref, map, move, drop | NLF_SdkModel.shared_deref/exclusive_deref read SAME cell payload; NLF_ViewLaws.map_token/map_read/map_release preserve token and compose the current-cell projection (not a cached payload). NLF_RefCell.shared_drop_valid/exclusive_drop_valid consume the live token, and NLF_CounterLaws.shared_current_counter/exclusive_zero give current-counter decrement / -1→0. NLF_MetadataLaws.release_payload/release_metadata preserve payload and all metadata. No clone/map_split/leak domain is claimed. Native typed return/move/deref/drop execute directly; no Ref/RefMut function is stub_verified. | All entry and Pool live guard scopes |
| Three-account TX1 exclusive-copy ABI | NLF_ThreeAccounts.tx1_snapshots: source-ordered snapshots 0,1,2 restore the exact initial State, advance fresh token allocation to 3, preserve Invariant, and retain exact replies/events. tx1_exclusive_copy derives the CP exclusive admission after those Drops, then a copy of the SAME supplied child bytes and Drop, with equal source/destination length. tx1_proof_public_frame derives disjoint proof/public frames from runtime key/cell identity. NLF_CopyStep.conflict/wrong_length/success additionally cover exact returned borrow error, unequal-length abort with guard live at the abort prefix, and successful copied state. | TX1:344; supports TX1:345 and TX1:328 parent assembly |
| Seven-account TX2 acquisition/cleanup ABI | NLF_SevenAccounts.tx2_acquisition_cleanup: source-ordered snapshots 0..6 restore the SAME State, advance next to 7, retain Invariant, exact schedule, ALL reply values (including deferred errors), and admitted account liveness. These are SEQUENTIAL source snapshots; each guard drops before the next acquisition. tx2_cell_identity proves aliases iff admitted keys are equal; no false distinctness premise is introduced. | TX2:241 and TX2:233; Pool seven-account folds |

Additional wrapper members: NLF_SharedLamportsLaw.result and
NLF_ExclusiveLamportsLaw.result select the lamports cell, not data.
NLF_DataLenLaw.result / panic_result and NLF_LamportsLaw.result / panic_result
cover the full returning Result or conflict abort of scalar getters and exact
Drop-before-return state restoration. NLF_MetadataLaws.key_projection /
owner_projection are direct full-key/full-owner projections. There is no SDK
method called data or owner: these are public fields in the pinned AccountInfo.

`NLF_TX1_Snapshot{0,1,2}.at_site` and `NLF_TX2_Snapshot{0..6}.at_site` are concrete
source-occurrence packets. Each carries its full previous event schedule,
precise cell/guard/token and payload, next-token count, runtime liveness and
source counterZero, not an independently chosen successful snapshot.

Global interpretation: a Cell stores its COMPLETE distinct reader-token list
and at most one writer. Valid excludes readers with a writer; Unique excludes
the same token in different cells; Below bounds every live identity by the
monotone fresh allocator. Every acquire/deref/release preserves Invariant.
NLF_ProgramFold.fold_invariant composes those steps in source order; mathematical
write-frame preservation does not license a write through an invalid/native
shared reference. Legal native writes still require a live exclusive guard.
NLF_SdkBorrowLaw.admitted_events installs empty tracking from the SAME runtime
admission, binds ALL initial counters using valid/freshGuards/noExternalBorrows,
and preserves the invariant through the fold. Runtime liveAccount,
sharedCellsOnlyEqualKeys and duplicateKeysShareCell supply actual cell identity.
The Pool uses the already-approved identical seven-field admission structure.
RuntimeCpiReadonlyEntry7 is neither assumed nor used.

Native pairings (all actual SDK bodies; no guard-return contract substitution):

| Native member | Pass | Matched failing control |
|---|---|---|
| Shared / exclusive free data guard | K001 / K003 | K002 / K004 |
| All data borrow conflicts, errors and error Drop | K033 | K034 |
| Shared/exclusive lamports, conflict mapping, scalar forwarding | K035 | K036 (wrong selected counter); K030 independently fails on false successful try_lamports |
| data_len/try_data_len, lamports/try_lamports, keys/owner, empty-data getters | K037 (K031 separately covers empty/error getters) | K038 (K032 empty-data control) |
| Shared / exclusive map and current projection | K039 | K040 / K041 |
| Seven shared tokens, current count and non-LIFO Drop | K042 | K043 |
| Three accounts, 1768-byte CP, arbitrary copy offset AND arbitrary observed byte, outside-frame and Drop | K044 | K045; canonical KMX pointer controls K005/K006 |
| Seven handles with mixed alias choices and every typed error-prefix cleanup | K046 | K047 |
| Shared / exclusive payload/lamport frame after Drop | K055 / K059 | K056 / K060 |
| Actual AccountInfo clone shares the data cell while metadata record fields remain distinct | K057 | K058 |

All copy-dependent runs use exactly KMX_copy_stubs.patch sha256
bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67.
No whole-buffer native copy proof is claimed: K044 is ONE byte window at an
arbitrary offset and arbitrary observer over a 1768-byte arbitrary prestate;
NLF_CopyValue.copy_coordinate/copy_frame/copy_whole reuse the canonical KMX
finite induction for value composition. Native allocation/ownership and each
caller's SAME source/destination association remain caller obligations.

Record fidelity is for the EXACT ScalarReply {value:u64,tag:u8} observation
shape only: K048 weak contract PASS; K049 inverted ensures FAIL; K050 real body
PASS; K052 unimplied caller assertions under stub_verified FAIL; K053 modifies
violation detected; K054 effect contract PASS. K051 is a code-generation
rejection (missing Arbitrary), NOT the failing control; the fixed same-named
K052 is the actual control. This calibration licenses no Ref/RefMut contract.

The native tests use safe live typed guards and bounded constructor partitions
(count 0,1,7 and the exclusive state; selected 2-byte payloads, plus K044's
1768-byte window). They do not verify Rust unsafe RefCell internals universally.
Universal counter/guard semantics and payload-size parametricity are the existing
std interpretation explicitly authorized by (be)(2); thin wrapper projections
and error mappings are transcribed line by line in NLF_CORRESPONDENCE.md and
calibrated against actual SDK code. No new runtime premise is introduced.

The final packet also derives the machine range: NLF_BorrowBounds.acquire_bound,
release_bound, step_bound and fold_bound prove -1 <= flag <= 2^63-1 throughout
all unsplit guard transitions from the installed empty ledger. The reusable
NLF_SdkBorrowLaw.admitted_counter_range pairs that derived bound with the SAME
runtime source-counter binding. It is not a fresh caller hypothesis and does
not silently treat an unbounded mathematical Nat count as a native isize.
