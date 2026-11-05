# NIK process notes

No SDK source bodies, harnesses or borrow traces were intentionally printed during SDK inventory; pinned inputs remain in evidence. Initial broad file/rule listings and ordinary commit output exceeded the requested one-line brevity; subsequent native/Lean operations used summary-only output.

The first SDK integrity check expected .cargo-checksum.json beside installed packages; it was absent. The lane-owned validation was repaired, without changing source/graph checks: validate cached .crate SHA256 against the frozen Cargo.lock, then compare Cargo.toml and src/lib.rs members to installed bytes. Both packages match; no SDK drift finding is claimed. NIK_SDK_CHECK.json preserves missing-sidecar diagnostics, superseded by NIK_SDK_ARCHIVE_CHECK.json.

The source graph was tightened to retain bare matching method names as candidates rather than resolving them to an unrelated internal function. Generic/indirect call edges remain unresolved and cannot support a reachability claim.

A transient NIK_CLIENT_ACTIVE marker was inadvertently captured in the model-stage commit while a client ran. It is removed from the final tree and explicitly ignored with only other transient/cache names; no evidence input is ignored. No prover was launched concurrently. All Rust/Lean attempts used admission allowed:true plus exit0 and the specified scopes. No timeout/cap increase, unchanged killed rerun or shared infrastructure edit occurred.
