# Measure strengthening: authority blocked, target not yet established

Branch: codex/pv-meas-20261029. Base: 946718387d.

## Completed and status

DESIGN.md preregisters privacy_headline_deployed_events_meas before proof work,
including arbitrary native probability laws, measurable decisions, unchanged
simE/completion/observer/bad event/T, unchanged bound and strict 2^-100 conclusion.
It identifies the required measured coupling step as well as averaging and
transport. The old per-environment theorem still has Fintype R; feeding it to a
new averaging lemma alone would not prove the requested strengthening.

lean/PV_MEAS_Average.lean contains DRAFT proofs of average_bound and
expectation_eq_of_equal_laws using Mathlib Bochner integrals. These have NOT
been elaborated, checked or audited. The #print axioms commands are requests
in uncompiled source, not audit evidence. Neither theorem earns proof credit.
No deployed headline, measured coupling or finite-uniform corollary is claimed.
No PV_EVH_ source was changed.

## Exact blocker and concrete requested extension

Common ruling h4 SCOPE makes the coherent privacy replay's external-object
manifest authoritative for EVERY external module and says a module absent
from all allowed authorities is a stop for that step. The actual host manifest
sha256 is d9187c800b7479f66ec6147e3c8e91c1158d382c4aa467bf678e76901b9a8c0e.
It has 5,673 entries, zero MeasureTheory or Probability entries. This independently
confirms the inherited external-authority gap recorded before source drafting.

The first blocked imports are:

- Mathlib.MeasureTheory.Measure.ProbabilityMeasure
- Mathlib.MeasureTheory.Integral.Bochner.Basic

A read-only source-import traversal (authority-extension-preflight.json) finds
203 additional external modules needed for these two roots, against Mathlib
revision 81a5d257c8e410db227a6665ed08f64fea08e997. All 203 have candidate objects
on the host. The traversal reaches 206 authorized frontier modules, whose object
hashes all match h4. This is NOT a complete new-object provenance/cohort audit:
the candidate objects are not yet authorized or loaded. Transitive authorized
imports still require the normal full manifest check before any compile.

The user has been asked whether to authorize extending authority to this pinned
Mathlib closure. No authorization has yet arrived. No external object has been
substituted or rebuilt to circumvent h4. tools/pv-meas-20261029/authority-preflight.py
is the exact read-only inventory script; its result includes source/object hashes.

## Before/after and ledger

Before: finite uniform rational environment/acquisition/native coupling laws;
finite-support representability obstruction. After: preregistered target and
unverified generic proof drafts only. The accepted theorem is unchanged.
Rows removed: NONE. Retained: all native source, joint acquisition, D163/D166,
V400, causal-prefix, observer, selected callback and original T obligations.
Added/changed assumptions in any accepted theorem: NONE.

## Validation and next deliverable

Lean attempts: 0/100; native: 0/0; Kani: 0/0. No IDs consumed, no capped scope
launched, no formal release result or axioms result. Wall/RSS/swap for a Lean
run are not applicable. Only source inspection, manifest/source/object hash
inventory and git checks ran. The host-restored flag exists; this is the h4
authority stop, not the historical host-rebuild gate or reservation contention.

Next: receive the explicit authority extension; verify the complete effective
closure with h6/h6'/h6'' namespace resolution; compile PV_MEAS_Average at 73100
under the prescribed caps/admission/failed-source guard. Then implement the
measured native/model coupling and finite-uniform integral bridge, compose
privacy_headline_deployed_events_meas, and run the reserved audits once green.
