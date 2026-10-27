# Final ELF gate method

Reuses tools/pv-runjoin13-20261027/build.py verbatim as
`tools/pv-runjoin14-20261027/build.py`, uploaded as the private gate13/build14.py.
The existing candidate source snapshot is reused; only the authorized shipped
file is copied from 05cb63a2ea589fe77b29444e2338ebbc505c3ad1. Its source-revision
file is updated. No second workspace or target cache is created. Existing
private SBF cache is reused, not the shared env-J tree. Per-build commands,
environments, admission logs, cgroup controls, timings, diagnostics and binary
comparisons are preserved. No binary/key/object is included in this commit.

The diagnostic Charon/Aeneas attempt ran first to determine whether any further
source repair was authorized; it failed on the next, outside-authority blocker.
The three ELF rebuilds then ran sequentially after the last source change.
No extraction result has been accepted as a release/source theorem. No unchanged
full replay or arithmetic Kani gate was run. `#print axioms` is N/A for all five
host scopes (two translations, three SBF builds), not a standard-axiom proof.
