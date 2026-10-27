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

The own receipt client initially fingerprinted only joint-directory direct
imports; Lean itself always used the correct env/J search path. During this
resume the receipt resolver was corrected to search joint objects followed
by the effective env/J LEAN_PATH, exactly as run2.py does. The sha256sum text
format is retained, so all-joint fingerprints remain unchanged. Earlier
missing-path entries are preserved as receipt gaps rather than rewritten
into invented hashes. No launcher, environment, scope or reservation script
was changed. An exact binary import inventory is planned to remove source-
scanner graph ambiguity before the three reserved final audit shards.

The explicitly recorded rebuilt-library Fmt source profile is 26ac770d…
(EJR_library-source-provenance.json), not daeafff8… from the separate formatter
repair snapshot with the same module name. The plan selection was corrected
before any Fmt replacement. Both candidate hashes and the reason are retained
in resume6-Fmt-profile-selection.json.
