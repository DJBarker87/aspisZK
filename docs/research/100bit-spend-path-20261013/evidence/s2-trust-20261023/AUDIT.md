# S2-T trust-boundary and conclusion-hiding audit

Scope: S2TrustedSdkBorrow.lean, S2TrustConsistency.lean, kani-spec/src/lib.rs.
The structure has exactly the fifteen route-B fields, in plan order. The only
Lean import in its dependency closure is Std. No existing Lean module is changed.

The field types and their transitive definitions do not mention adapter/caller
success, fixed proof/public/checkpoint bytes, caller outputs, logs, dV_frozen2,
or S2CallerFacts. The arbitrary Payload carrier represents local typed slice
contents, as the plan requires; excluding even local payload contents would
contradict cell_payload/shared_deref/exclusive_deref. No field fixes those contents
to caller data. Reply is a primitive library Result arm, never a caller output.
Ambient is an arbitrary type holding all unmentioned state. Exact primitive
frames preserve it; this is not an assumed final caller accountFrame.

| Field | Mathematical / Rust spec content |
|---|---|
| account_data_cell | Handle-to-cell identity, alias retention, separately admitted data/lamport geometry |
| cell_payload | Full typed descriptor and current arbitrary element map, including empty slices |
| cell_counter | Same cell's signed counter and live-token ledger, external borrows retained |
| shared_ok | Nonnegative nonsaturated acquisition, one fresh token and one increment |
| shared_err | Negative/saturated counter: exact primitive BorrowFailed, no state changes |
| exclusive_ok | Zero-only acquisition, -1, one fresh exclusive token |
| exclusive_err | Every nonzero counter rejects unchanged |
| shared_deref | Exact current payload, no writes |
| exclusive_deref | Exact payload and one bounded element write with exact footprint |
| guard_move | Same token/cell/descriptor, one owner location changes, source ownership removed |
| shared_drop | One live shared token consumed, same counter decremented, payload retained |
| exclusive_drop | Unsplit token consumed, -1 to 0, current written payload retained |
| error_move_drop | Err owns no guard and leaves the complete state unchanged |
| borrow_frame | Exact reference primitive transition; preserves ambient metadata/Rc/oracle state |
| guard_liveness | Related live guard allocated with the same descriptor; primitive frame retains this |

`Library.related` is the EXPLICIT trusted typed interpretation relation. It is
not instantiated for Rust by this packet. A production instance must tie the
observations to actual AccountInfo/RefCell/Result/guard provenance and lifetimes.
The mathematical model's Eq relation is labelled only as a consistency witness.
Runtime P6 separately establishes valid initial admission. `Valid` includes
linear-token uniqueness, current payload descriptors, actual allocation, full
signed bounds, external-borrow accounting and data/lamport separation for live
accounts. `Enabled` excludes stale/absent tokens, occupied destination owners and
out-of-bounds/nonexclusive writes. Those are legitimate-library-context conditions,
not acceptance or successful-borrow hypotheses. Conflict and saturation are in
scope. No claim of validity for arbitrary hostile Rust byte patterns is made.

No clone/split/leak, Rc acquisition/destruction, realloc/free, lamport borrow,
concurrency, reentrancy or CPI operation exists in Op. An encountered excluded
operation requires proof or an explicit enlargement of the authorized trust item.

Rust is a bounded projection (CELLS=2, TOKENS=3, WIDTH=2), with full i64 counters
and arbitrary payload/descriptor/ambient values. Its verified-against contract
covers the complete primitive relation and successor validity in that projection.
It is usable by `stub_verified(step)` in that checked domain. Larger caller
capacities must be instantiated and checked; neither width-two verification nor
the model alone licenses production buffer substitution. No Lean/Rust extractor
correspondence or automatic Drop lowering is claimed. Later workers must supply
per-call simulation and actual implicit-cleanup order. This is the specification
work package, not the common execution certificate or Required14 instance.
