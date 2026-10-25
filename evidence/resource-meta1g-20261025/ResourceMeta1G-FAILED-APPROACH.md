# Retained first focused-suite failure

Source043c7b49ab; exact command, source hashes and metrics retained in
ResourceMeta1G-focused-v1-receipt.json. Exit1, wall0.7383737079799175s,
peak39026688B, swap0; axioms N/A. Full log and failed test source are retained.
Eight tests: two fixture failures, one fixture error. No operational source error
or resource failure was observed; normalized bytes/full-AST test passed.

The unrelated-job fixture used the pure node helper's default pids_enabled=False
beneath a root delegating pids. The immutable observer correctly rejected it with
pids delegation mismatch. Set the synthetic job's pids_enabled=True,
pids_current=0, tasks_max=64, retaining its8GiB cap/current and all other jobs.

macOS tempfile paths used a symlink spelling (/var versus /private/var), so actual
bootstrap/stage parent.resolve()==parent correctly rejected two tests. Resolve
the temporary parent before embedding it in the stub payload and fixture. This
corrects fixtures without relaxing the production path guard.

Only test fixtures change for v2; operational modules, pins, policies, expectations
and finite delta manifest are unchanged. No host action, admission or marker ran.
