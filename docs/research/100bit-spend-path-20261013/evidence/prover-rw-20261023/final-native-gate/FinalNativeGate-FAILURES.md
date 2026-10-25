# Retained failures and limitations

Historical Kani059 remains failed (exit124;240s timeout; approximately3.38GiB
sampled aggregate in retained resources). FinalNativeGate-retained-059.json
preserves exact target/argv/source dependency fingerprint, result and wall time.
Its time-wrapper15840KiB is not substituted for whole native aggregate RSS.
No timeout/cap increase, retry, or new Kani invocation here.

Fixture001: pinned generators' default argument G was not supplied to the local
fixture namespace. NameError before test execution. The first inline runner only
caught SystemExit, so wall/RSS/swap and the test source overlay were not recorded.
Those metrics are explicitly null, never pass/zero. The tool-returned traceback
was ResourceRssGOv3-reviewed-functions line13: NameError name G is not defined.
Its log was opened but empty because exception escaped the redirected context.
Fix: add G to the pure fixture namespace; improve runner to catch all exceptions.

Fixture002:19 tests attempted,16 setup errors because macOS Python has no
os.pidfd_open attribute. Full failure log and measured receipt retained. Fix:
create mocked Linux-only os.pidfd_open and signal.pidfd_send_signal attributes;
no Linux process/syscall was executed. Fixture003 then passed19 tests.
Fixture004 added real pin-decision tests and passed27. Fixture005 covered the
bootstrap-seal/source-pin split and passed27 after that source change.
Fixture006 added retention of failing raw controls and an rlimit drift check;
28 passed. No unchanged full policy suite was executed. Receipt source_revision
string4008aeadf2d-source-overlay in003–005 has an extra trailing d; the exact
base is4008aeadf2, and each receipt's per-file SHA256 overlay is authoritative.

All filesystem/process/systemd/identity/controls/guard boundaries in the fixture
body are mocked. Real unchanged policy.evaluate consumes small raw snapshots;
source gates use explicit finite file/runtime/tree/env mocks. Mocks do NOT prove
fsync persistence, kernel pidfd semantics, Linux lifecycle, compiler/Kani source
semantics, fresh live admission, runtime effects, performance or security.

Missing host runtime/native dependency closure/cache/env/rlimit fields cause
actual source _plan to deny. No host query/upload/setup action was attempted to
fill them. Public entries remain disabled regardless. A future lead review
must assess the exact setup diagnostic, all source changes and independent
bootstrap pin, then allocate execution separately. No owner permission question
or implicit authority follows from preparing these files.
