# Final source020 and v5 release review

This final candidate supersedes the first local source019/v5 build. Source019,
its manifests, failures, successful receipts and byte-identical reproduction are
retained, including the complete first release in the private location named by
`FinalNativeGate-v5-superseded-019.json`. No historical v1-v4 artifact changed.

The behavioral and trust-boundary account in `FinalNativeGate-V5-REVIEW-019.md`
continues to apply, with this additional correction: the collector now completes
`project(phase, report)` BEFORE clearing/updating its initial structured unknown
record. An exception in projection therefore retains phase/status/allowed=null/
reporting_failed=true while the existing exception path forces failure. The
initial candidate could leave an empty admission history entry in this case;
that approach is rejected and its beforeimage is preserved. New focused fixture
`test_projection_exception_keeps_structured_unknown` exercises this boundary.
No policy/context/permission assumption or guard is relaxed.

Final complete before/after functions/constants, maintained source hashes,
plan/bootstrap/seal hashes and v5 transfer root/receiver/transport/payload pins are
in source020 evidence. The final overlay still changes exactly two setup mains
relative to the maintained final source plus four regenerated plan/seal records.
Relative to historical v4 there are explicit compact reporting, no-owned cleanup,
private raw publication and staging-root changes; no byte-identity assertion.

The old report reason and new remote staging absence remain UNKNOWN. All host,
upload, setup, query, native, compiler, Lean, Kani, ELF, key and RPC actions are
zero. Local permission fixtures only create private test files and temporarily
restore umask002/777; they do not modify existing host permissions. Reused source
policy/runtime mock pins are source evidence only. Standard Python/OS operational
trust and every SDK/std/runtime/allocator/extraction/sourceDrop/child/mark/P2Prime/
native/artifact/security join remain retained and open; targets NOT ESTABLISHED.

Next deliverable: lead source020/v5 review, then ONE separately allocated future
v5 DATA action only. No remote action is authorized or performed by this worker.
