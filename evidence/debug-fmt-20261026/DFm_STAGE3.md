# Structural preservation, provenance and unchanged ledger

DFm_parser-semantic-comparison.json compares complete retained type/value
expressions, universe parameters, reducibility hints, safety, references and
axiom lists. All 212 retained declarations match after precisely seven compiler
matcher name substitutions and erasing binder names. Shared matcher definitions
are themselves compared, not merely assumed. This is a structural expression
comparison, not a new Lean equivalence theorem. Raw object identity fails as
recorded in stage 2. The literal deletion removes 72 declarations net across
both modules: two source definitions plus 18 native axioms and 16 proof helpers
per module. The shared axiom-free matchers are retained under regenerated names.

DFm_source-reference-audit.json scans the selected RPz2 graph's 1,489 exact
hash-matched local sources. Only the two generated Funs files explicitly mention
the formatter symbols. This is lexical evidence, not RPz3's proof-term-to-top
reachability audit and not a compile of 1,487 transitive importers.

DFm_EXTRACTION-PROPOSAL.md supplies concrete proposed Debug exclusion flags,
with the pinned Charon source's syntax and trait-filter limitation recorded.
The selected record parser provenance is header-array F; the older E crate cited
in stage 1 is a sibling, not the selected source. Original F and prefix-E crate
source/commands, Aeneas's Formatter axiom and default native toStr bound proofs
are now pinned in the provenance JSON files. No extraction was rerun.

DFm_prepare.py reproducibly prepares only evidence copies. The zero-context
patch targets the canonical committed Lean copies whose hashes equal the replay
selection. `python3 DFm_prepare.py --check` and
`git apply --check --unidiff-zero DFm_remove-debug.patch` pass without applying it.

DFm_before-after.md gives the complete identical Rc8_Top.deployed statement.
DFm_ledger-delta.json re-counts the inherited 126 rows with the same identity,
class, scope and aliases. Raw actual 83T/19P/13G, distinct 83T/18P/13G;
combined non-alias raw 89T/23P/13G, distinct 89T/22P/13G, all unchanged.
No fresh kernel leaf expansion or top proof replay is claimed. Conditional
Rc8 non-vacuity/positive margin and non-universal collision remain inherited;
JFt_'s full joint witness is still open. Premises removed/added/changed 0/0/0.

Importer phase admission succeeded, but before launching Lean, its dependency
pin preflight found missing historical ExtractedPrefixTypedFullCurrent. That
uncompiled sample was replaced by available ExtractedPrefixFrameAgreement; the
six direct importers remain in scope. This did not consume a Lean attempt.
The unchanged systemd-run shim is now waiting outside a scope for the 17:45–
18:15 UTC quiet window; no quiet marker or admission infrastructure was edited.
No shared source/object was overwritten, and no cap was raised.
