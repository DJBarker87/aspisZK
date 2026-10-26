# Stage 5: successful source decode canonicality and validator loops

JFu_DigestCanonical.source proves EVERY successful emitted digest decode returns
canonical limbs. JFu_DigestCheck.source proves the corresponding native
canonicality loop returns true. JFu_DigestSliceCanonical.source and
JFu_DigestSliceFacts.source extend this to the actual cast/unwrap/decode sequence,
with exact source byte contents retained. JFu_FrontierCheck.source proves the
native20-digest snapshot frontier check. JFu_SnapshotValidator.source proves the
complete snapshot validator from its explicit metadata predicates and canonical
root/frontier; the real-byte metadata instantiation is still open.

Attempt065 reached the default heartbeat limit in repeated context-wide simp.
It was NOT rerun unchanged. Replacement066 isolates Result branch inversion;
067 uses eight applications of that lemma and direct finite-index projections.
067 succeeds in8.10s with standard axioms. No cap/heartbeat/depth was raised.
Other failed elaboration attempts are retained as rejected evidence.
Exact per-attempt receipts supply revision,target,source/object hashes,exit,
wall,RSS,swap,command,cgroup caps and all printed axioms.

No native wrapper, global owner law, or top premise is discharged by these
forward primitive facts alone. Delta from Rc7 remains zero in every class.
