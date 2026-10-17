# Actual tx1 extraction and pending source proposal

`prepare.py --out input [--check]` re-extracts exact complete actual tx1/verifier mark and approved Prepared source from pinned revision3335 over the existing canonical carrier. Source-body hashes and explicit boundary list are in `input/source-pins.json`. Typechecking stub bodies have no theorem semantics. `run-host.py` runs only focused capped Charon/Aeneas, validates LLBC and records exact receipts.

The actual caller's while loop blocked Aeneas; see `../../evidence/tx1-caller-blocker-20261016/README.md`. No Lean result is claimed. `proposal-tail` contains a concrete review-only untested helper patch and ownership/tail hash audit. `propose-tail.py` generates it without applying it. The production candidate has not adopted this proposal; no rewritten extraction probe may run pending source approval.

Decision1c subsequently approved the exact tail proposal and source e5c186ba3 applies it. Final input is `input-accumulator`, reproduced with `prepare.py --out input-accumulator --actual-accumulator [--check]`; input and input-approved are frozen predecessor diagnostics. The final coherent Type/Funs/model/proof audit and green receipts are in `../../evidence/tx1-caller-accepted-20261016`. The next verify-helper source proposal, if any, requires its own decision.
