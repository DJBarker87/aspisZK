# Stream B ledger tools

Run `python3 tools/pv-ledger/check.py --check` (or add `--json`). Without
`--check`, violations are still displayed, but exit status is informational.
The inventory and drafts are reproducible with `enumerate.py` followed by
`build-ledger.py`. These generators intentionally reset progress to the pinned
initial assessment; do not run them over later accepted closure edits without
reviewing the diff. No Lean sources or proofs are generated.

The checker pins the enumeration, prevents dropped rows/edges, verifies the
retained emission hashes, validates draft contracts and candidate statement
artifacts, and reports totals. Historical sources and receipts are read using
`git show <full revision>:<path>`, independently of sparse checkout. Branches
must contain the cited revision; a branch advancing does not move the pin.

A future CLOSED row supplies `closure`:

- `theorem`, `branch`, and `source` with `revision`, `path`, `sha256` of the
  committed theorem file. BODY theorem name equals the draft's expected name.
- `statement`: the same pinned-reference triple for a JSON artifact with
  `format: pv-ledger-printed-statement-v1`, `theorem`, `source_sha256`,
  `printed_statement`, `printed_statement_sha256` and ordered `binders`.
  The text is verbatim #print output, not reconstructed source. Every leading
  binder has `verbatim`, `role` (`parameter` or `hypothesis`); parameters have
  `type_checked_non_proposition: true` from the statement audit. Hypotheses
  have a B-y `category` and exact named `fact`/`ruling`, or this row's Pre, or
  `leaf` and the actual `request` text for a LEAF returned case.
- `raw_audit`: pinned reference to a complete strict-walker receipt, with
  `mode: raw_walk`, `source_revision`, `complete: true`, zero unresolved
  constants, empty failures and augmented mismatches, positive equal
  requested/completed root counts, and `standard_axioms_only: true`.
  Its exact theorem root records `source_sha256`, `equal: true`,
  `standard_axioms_only: true`, and `walked_axioms` within the three standard
  axioms. Add source association fields in a normalized receipt when the
  historical walker output lacks them; preserve and cite the original raw
  walker receipt rather than relabelling summary-based #print axioms output.
- `raw_audit_source_sha256`, the exact `boundary`, ordered
  `all_reply_branches: [returned,failure,divergence,pending]`, and
  `frame_proved_by_shape: true` from the statement/proof audit.
- `callee_instantiations`: one entry for each BODY child, naming its CLOSED
  theorem, `actual_arguments`, `entry_state`, and literal `source_excerpt`
  containing the application. Cyclic CLOSED composition is rejected.

LEAF closure boundary is `LEAF_FULL_REPLY`; function BODY boundary is
`CALL_ENTRY_TO_RETURN`; OwnInit composition boundary is
`ORIGINAL_ENTRY_TO_OWNINIT_CASE_SPLIT`. No present row supplies a closure.
The printed parser supports bracketed named binders, including leading forall
binders. It rejects anonymous arrow premises and unsupported binder formats;
provide full named printed binders rather than bypassing the inventory.

This is an evidence-integrity checker, not a Lean elaborator or a semantic
proof auditor. It cannot establish that an arbitrary named Prop hides no
assumptions, that an application is logically sufficient, or that a declared
frame was actually proved. Those are mandatory statement/raw-proof review
obligations. The checker checks their concrete receipts, named statement
binders and source applications and fails closed on missing evidence. It never
promotes an OPEN/PARTIAL result automatically. Review the statement definitions
and the raw proof before adding a CLOSED receipt.

Tests: `python3 -m unittest discover -s tools/pv-ledger -p 'test_*.py' -v`.
Synthetic positive/negative receipt controls are test data only, never formal
proof evidence. Controls cover missing theorem/audit root, unresolved constants,
wrong audit revision/source, nonstandard axioms, summary-based audits, omitted
or forbidden hypotheses, OPEN callees, missing frame/pending, and row deletion
or graph mutation.
