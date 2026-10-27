# Recovering missing provenance artifacts

The initial scan found 80 current project objects without a successful receipt
that binds the current object hash to the expected source hash. Host source
copy equality alone cannot fill that gap. R1NaturalProjection was tried first
as required and rejected; its protected source has not been edited.

For the other exact gaps, resume6-rebuild-gaps.py requests one dependency-first
source replay to recover a missing hash-bearing evidence artifact, the explicit
AGENTS.md verification-cadence exception. Sources already on research are taken
from the pinned HEAD blob; branch additions use their tracked branch bytes.
The existing launcher receives the real current direct-import object hashes,
without a nonce or invented dependency fingerprint. A duplicate-input refusal
is recorded and respected, never bypassed. A failed/killed source is not
retried unchanged. Each accepted output has its own recorded SHA-256.

This repairs provenance where possible but does not certify the unrepaired
protected projection or its stale downstream closure. The final gate must
continue to state every exact remaining gap, including external package gaps.
