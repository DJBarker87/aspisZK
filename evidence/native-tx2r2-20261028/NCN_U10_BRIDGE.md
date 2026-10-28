# NCN U10 continuation

U10 OPEN; deployed target not yet established. Import all scoped NCI U10
results without reproving them. No parent dictionary is declared installed.

NCN_K010/K011 and K012/K013 prove exact residue_limb_at/power_limb_at
contracts with inverted-ensures failing controls. Their domain is index<4 on
arbitrary four-word records. The user-approved call-site contract route is used.
NCN_K009 failed code generation because an owned harness compared u64 and usize;
NCN_getter_fix.patch inserts the required u64 cast, preserving the invariant.

NCN_K014 one-product/add/write under the complete cadence invariant timed out
at90s: zero credit; K015 was never launched. Replacement splits native widening/
product transport from arbitrary checked addition/frame under the explicit
no-overflow domain. The existing NCI bounds establish that domain for callers;
no stronger invariant is adopted.

NCN_L001 compiles NCN_ModelStep.product_write: exact checked emitted casts,
product, addition and array write with selected indices and exact List.set
contents. It REUSES NCI_ResidueWords, NCI_GetterModel and NCI_ArrayFrame.
Axioms [propext, Classical.choice, Quot.sound]. Vec/iterator native association
and full push/finish/accumulate remain open; this local source-model composition
does not discharge them or create a whole-call output premise.

Per-attempt target/source/dependency pins, command, exit, wall, RSS, swaps and
axiom lines are in NCN_ATTEMPTS.jsonl and individual receipts. Frozen source,
model headline, approved assumptions and ELF pins are unchanged.

NCN_K028 isolated widened product timed out90s; zero credit and K029 unrun.
NCN_K030/K031 establish native checked addition and exact selected-cell write/
arbitrary other-cell frame under raw<=MAX-product. NCN_ReaderDomains.word_add_domain
(L003) obtains that precondition from the existing cadence bound. The primitive
product remains OPEN natively; no multiplier body or new field-product stub
is credited. Existing NCI checked word arithmetic and induction remain reused.

## Native Vec64 and the next split

K055 failed a harness-setup unwind assertion in generic Arbitrary array64
construction, not a source assertion. NCN_setup_fix.patch expands the SAME64
arbitrary rows as a literal (no domain change, no cap/unwind/timeout increase).
The unchanged harness names are retained. K056/K057 then PASS/FAIL as required:
actual Vec index on a valid arbitrary64-row allocation returns the selected
four-U64 row, with source frame, terms and Vec pointer/length unchanged.
This establishes the successful valid-allocation index window; it does not
prove heap::filled failure/initialization/ownership or arbitrary SDK heaps.

K058 full64 native value with original-array copy plus modulo reference timed
out90s. Zero credit; no unchanged rerun. Next split is a pure-record Vec row
function contract, then the actual value body through stub_verified. Its matched
contract/caller controls are required before credit. The contract wrapper's
cfg erasure restores the exact frozen self.raw[index] expression.

## Final stage and authoritative status

**U10 remains OPEN.** K059/K060 prove/control the pure four-U64 row getter
contract on valid64-row Vec inputs. K061/K062 then pass/fail for the ACTUAL
value body through stub_verified, with the exact paired reducer. For any
index<64, every returned limb is the SAME selected row limb modP. This removes
NCI's one-row/VecRow64 limitation for the local value bridge. It does not prove
pending construction, runtime allocation or the enclosing installed dictionary.

K063/K064 establish one exact native constructor iteration on arbitrary64-row
and64-weight pre-state, all indices and other-row frame. K065 finish on an
arbitrary global enumerate pre-state timed out90s; K066 was not launched.
The pre-state was built by nth(i-1), then ONE actual next/write, with the
verified row getter. No whole finish loop was attempted. Next split: a weak
record-returning value contract plus reply-log/iterator transport, selecting
its real value through the CLOSED value bridge; no repeated modulo arithmetic
inside the iterator proof.

After Kani exhaustion, L016 proves the exact Usize mask/flush cadence,
NCN_Cadence.word_mask/flush; L023 proves checked mask/shift/add returns exactly
the one-fold natural value and <2^34, NCN_FoldWord.source_ok. These reuse NCI's
bounds and word construction, and remove the remaining independent arithmetic
alignment work. L017/L018/L019/L021/L022 are excluded drafts/inspections;
L020 is successful standard-library inspection. No generic library or launcher
was edited. L024 co-imports/audits all77 selected old/new top theorems, standard
axioms only. This additional final audit is justified by the new cadence/fold
modules, rather than an unchanged regression.

| Member | Final native/cohort scope and remaining implementation work |
|---|---|
| F099 finish | OPEN: complete model traversal reused; native iterator/count/writeback/frame/ownership transport still missing after K065. Needs a split native gate, not another model induction. |
| F100 new | OPEN: arbitrary64-cell native initializer step closed; FilledRows64 allocation/error/cleanup, Vec mutable-index borrowing and full source-loop association remain. |
| F101 push | OPEN: exact mask cadence and model arithmetic are checked; selected-row borrow/frame, unchanged terms and call association require UpdateRowNative and a native parent cut. |
| F102 value | CLOSED local valid64-row helper through the row contract and paired reducer; actual parent/dictionary installation remains OPEN. |
| F108 accumulate_batched_with_node | OPEN: NCI basis/node/flush and model invariants reused; actual six-stage/64-push iterator/port/frame association, once-only terms update, rhs/power/next and trace transport require native work and PushNative. |
| F109 accumulated_weight_at | Existing CLOSED local helper imported unchanged; parent op12/index/carrier association remains in F108. |
| F110 basis_at | Existing CLOSED local helper imported unchanged; parent op13 association remains in F108. |
| F120 power_limb_at | CLOSED local and now contract-checked K012/K013; whole update-row tuple association remains. |
| F123 residue_limb_at | CLOSED local and now contract-checked K010/K011; whole update-row tuple association remains. |
| F125 update_residue_row | OPEN: native add/write and old native flush window, exact checked model product/fold and cadence are available. Native integer product/tuple/4-limb borrow/frame/conditional-flush association remains; K014/K028 have no credit. |

These retained implementation gaps need new native evidence or an actual lower
allocation/ownership bridge. No independent uncompiled arithmetic, modulus,
mask/shift, bound or model traversal fact remains from these attempted rows.
No new cryptographic hypothesis, security metric or target is introduced.

Final evidence summary:70/70 Kani and24/70 Lean. L024 is the final77-theorem
co-import/axioms audit (61 unchanged NCI and16 new), exit0, wall2.176507547032088s,
peak RSS5,357,996KiB, swap0. NCN_VERIFICATION.json validates each exact-source
receipt. The budget stop includes the independent post-Kani cadence/fold work;
all remaining per-member tasks above need native implementation association.
