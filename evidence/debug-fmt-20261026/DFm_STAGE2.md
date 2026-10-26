# Filtered parsers compiled; matcher identity qualification

DFm_002 and DFm_003 compiled both filtered Funs modules in the isolated host
DFm_objects overlay. DFm_005/006 audited original/filtered objects and retained
full #print axioms output. Every filtered declaration is standard-axioms-only.
DFm_parser-comparison.json records the exact expression comparison.

The strongest literal "every other declaration unchanged" claim is FALSE.
Two Error equality definitions reference a shared compiler-generated matcher
under CoreFmtDebug.fmt.match_1 in the original object. That matcher is axiom-free
and not exclusively used by Debug. Filtering the source causes Lean to generate
it instead under CoreCmpPartialEqError.eq.match_1; five other match_3 helpers
become match_2. Nine shared declarations consequently differ in expression
constant names. The public parser source bytes outside the two deleted blocks
remain identical. Semantic equality modulo compiler-helper renaming is still
being checked; literal object-byte equality must not be claimed.

Failures retained: DFm_001 failed import resolution before checking any parser
because Lean selects a namespace directory from one LEAN_PATH root. The corrected
artifact selection reuses pinned Types objects through DFm_-overlay symlinks,
recorded in DFm_type-object-selection.json; the next invocation had different
selected dependency paths. No shared object or source was overwritten.
DFm_004 failed the inspection module's Repr ReducibilityHints request; the audit
source was corrected to encode its constructors explicitly. No timeout or memory
kill occurred; no failed source/environment was retried unchanged.

Budget so far: 6/40 Lean attempts (4 passed, 2 ordinary setup/type errors), 0 Kani.
No release claim, top theorem edit or premise removal; ledger delta remains zero.
