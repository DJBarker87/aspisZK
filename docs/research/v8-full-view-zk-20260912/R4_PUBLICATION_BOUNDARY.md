# R4 publication boundary and attempts

Date: 2026-09-13.

The research module `v8_privacy_publication` introduces an immutable private
candidate bound to the exact body, public statement digest, source/profile
digest, gate-version digest, mask nonce and schedule digest. A full-view review
is unforgeable outside the module. A stale review or different body fails, and
the only byte sink consumes an approved candidate.

The current review function returns either `RawPrecheckRejected` or
`CompleteFullViewCoverageUnsupported`. In particular, raw affine PASS cannot
create a permit. This is intentional safe containment, not a completed repair.
The test-only constructor exercises stale-body and consuming-sink invariants;
it is unavailable in non-test builds.

The existing entropy implementation separately confirms that:

- a preselected nonzero public nonce receives two fresh OS-random 32-byte
  private components;
- reservation precedes mask/salt derivation;
- a durable nonce remains burned across store reopen and across statements;
- concurrent reservations have exactly one winner;
- the field-mask and leaf-salt domains are separated.

The selected generated harness still uses deterministic secrets and an
in-memory store. Its observed external paths write public/transition/binding
setup files, diagnostic logs and—only after local verification—the proof body.
No production return/upload/account path is authenticated by the available
source closure.

R4 therefore provides a reviewed fail-closed boundary, but not a useful q22
adapter: no full-view review can currently be issued, and retrying an
unsupported mathematical scope is forbidden. Wiring fresh production attempts
must wait for the R3 H1/C2 conditional-law theorem and a source-linked complete
gate. The public setup/account events must remain in the eventual retry view.
