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
