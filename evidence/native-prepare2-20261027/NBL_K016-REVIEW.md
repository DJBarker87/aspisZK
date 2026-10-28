K016's new view-rejection source cut FAILED its expected Error::Parse check;
cover after that assertion was unreachable. K017 fully qualifies both the
callee and stub target but has the same failure. Neither gate receives credit.
This is unresolved harness/stub association, not evidence of a frozen release
counterexample: the intended replacement must first be proved to be reached.
Original outputs/source/graph/lock receipts are retained, and the native Parse
caller composition remains OPEN. No result was relabelled as passing.

K018 adds an explicit replacement-entry assertion; it passes, but the Parse
identity still fails. K019 requests regular output/CBMC trace and replaces the
final match with distinct success/error cases: the shared assert_eq panic
property fails, while the unexpected-success branch is not reported failing.
The output does not provide a usable concrete trace explaining that error
identity. This unresolved stub/caller association is preserved as a finding,
not assumed away or attributed to frozen Rust.

K020 isolates by POSITION: the continuation receives the already-returned
typed View Result instead of stubbing the borrowed-View-producing function.
On Err(Parse), the exact '?' + semantic/new continuation returns Parse,
performs no digest and preserves arbitrary old scratch. PASS6504 checks and
one cover,21.669329446s,794960KiB,swap0. It is local Result propagation credit
only; the end-to-end native wide_view stub/caller gate remains excluded/open.
No arithmetic certificate is claimed from failed K016-K019 or K020.
Own runner gained an optional NBL_KANI_TRACE=1 diagnostic output mode for
K019; validation/graph/lock/caps/timeouts remain identical.
