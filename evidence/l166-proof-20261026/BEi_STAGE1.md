# Operational cut and recorder laws

Checked source-language operational relation, soundness, completeness,
uniqueness, chronological prefix preservation and sequential composition.
The recorder delta is the exact ordered suffix at the same cut, including a
failed/diverging syscall. CutProjection supplies source/ROM prefix transport
once operational step evidence is available.

These are proof rules for an explicit small-step relation, not the concrete
physical batch instance. No L166 or actual-root premise removal is claimed.
All successful declarations use only the three standard axioms. Attempts004
(reserved identifier) and006 (pair projection rewrite) failed elaboration;
changed proofs passed005/007. The incomplete006 audit printed sorryAx and is
EXCLUDED from accepted evidence. No source contains sorry/admit/axiom.

Nine Lean attempts including failures, zero Kani; no timeout/memory kill.
Attempt006's first reservation scan encountered a vanished cgroup; the required
30-second retry succeeded before any source upload/compile. Both scan logs
are retained. All launched scopes have terminated. Per-attempt receipts pin
source/dependency hashes, revision, exact command, limits and resource metrics.
