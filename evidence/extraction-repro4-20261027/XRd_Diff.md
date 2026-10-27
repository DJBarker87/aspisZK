# Release/cohort comparison blocked at translation

The selector-only LLBC 80465ea3… contains the required structured bodies;
XRd_llbc_inventory.json pins every function body and XRd_kit.json identifies
the required subset. This fixes the inherited missing-LLBC-body obstruction.
It does not establish a Lean declaration or a release/cohort equality.

The pinned translator fails at checkpoint (XRd_002/003). The selector-only
independent subkit with checkpoint opaque then fails at prepared_claim
(XRd_005). No Types/Funs is emitted, so a complete fresh declaration-level diff
cannot honestly be supplied. XRd_declaration_diff.json retains EVERY selected
cohort declaration: 45 Types and 87 Funs, all association status UNPROVED.
These are a conservative superset of closure uses, not new proof-term reachability.
The exact coherent selected producer paths/hashes are retained from XRc.

No alternate producer, old raw output, incomplete XRc boundary output or LLBC
body is substituted as fresh release Lean. Inherited observations remain:
Prepared.new threads scratch; prepared_claim consumes powers29 rather than
gamma; QueryGeometry adds line_z; Dot drops count; release tx1 replaces the
retired dispatch and deferred query/finish interfaces differ. Their exact source
quotes remain in extraction-repro2. None is a new inequality/equality theorem.

XRd_Association.lean is not manufactured: the requested concrete release
function declarations are unavailable. No desired equality is asserted as an
axiom, placeholder, arbitrary dictionary field or theorem hypothesis. The
inherited error-enum carrier theorem remains valid in its isolated scope;
recompiling it would add no association progress. Concrete unproved function
Props cannot be type-checked against missing declarations; their exact
remaining interfaces and obstructions are in XRd_OBLIGATIONS.md.
