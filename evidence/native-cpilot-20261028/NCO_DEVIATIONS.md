# Own input corrections

K017–K020 compiled no harness: NCO's nested-module declaration lacked an
explicit path. The serial queue was not fail-fast on compiler verdicts. Fixed
NCO_instrument.py to add #[path="NCO_wire.rs"]; these are excluded failed
input attempts, not repeated timeout/memory failures. Future independent
queues inspect the first compile before submitting dependent checks.

E001 paired Charon v0.1.299 with Aeneas expecting v0.1.223. Rust reference
compilation passed; translation failed its version check. Corrected the OWN
extraction script to the co-located XRa_bin/charon companion. No host/lead
infrastructure or shared tool changed. E001 is not extraction evidence.

Vec K015 body contract passes but has no copy fidelity credit (no matching
KMX control yet). K016 stub generation rejects Vec<u8>: Arbitrary missing.

K021–K024 compiled no harness because a second execution of the OWN
instrumentation script doubled pub(super). The transform is now idempotent;
K025 corrected body contract passes. No verdict renaming or increased cap.
E002 with the matching XRa pair reaches an Aeneas internal borrow error at
slot_offset_ref's array read (InterpBorrows.ml:2731). E003 isolates the two
branch-only references and succeeds. No translator patch is made.

K041 is an OWN repeated visibility-transform input error; fixed the parser
setup transform to assert visibility rather than adding it again. No prover
body ran. K038 TIMEOUT is not repeated unchanged: subsequent parser checks
split the declared contract domain into header≤5 and row2/length37 cases.
Those domains are diagnostic restrictions and do not cover every real caller.
L004/L006 default-heartbeat failures are excluded. No limits were increased;
L009 replaces broad simplification with the existing checked constant laws
and the reference's matching pattern structure.

K042 compiled no target: the OWN upload batch included the expansion harness
before its contract annotations had been installed in scratch compact.rs.
Installed both sets of scratch annotations before the next launch.
K043 (header≤5 full result/pointer relation) and K045 (header status only)
time out. Neither shape is replayed. K046 isolates the disjoint exact row2,
length37 branch and gives unreachable loops a checked unwind bound2; it is
not a rerun of the unrestricted/header shape. No caps/timeouts increased.
No credit is inferred from any restricted parser contract for general callers.

Read-only host inspection used extra SSH sessions while an earlier proof
transport was open. This was a transport-rule deviation, with no second build
scope, mutation or resubmission; subsequent host work is serial through the
lane wrapper. Sources, evidence and caps are unaffected.

K046 compiled no target because the exact KMX include and NCO's own Vec
import duplicated a name. Removed NCO's redundant import, preserving KMX.
K047 corrected exact-row2 split still TIMEOUT; it is not replayed.

Final scalar receipts K048–K055 use a stricter archived source pinset and
include compact.rs itself (earlier compact receipts did not snapshot that
file individually). Earlier receipts remain evidence toward the final packet,
not substituted for the complete final source pins. Wrapper sources and the
current complete pinset are archived from K047 onward.

Top-level raw scratch harness sources were initially retained in the evidence
directory. They are now represented only by NCO_harness.patch; receipt source
snapshots are preserved. Own setup/runner scripts decode that patch directly.
No repository crates/ or programs/ source was changed at any time.

K062/K063 use inverted/weak postconditions on the same32-byte body layout
following K060's timeout. They were distinct fidelity queries, but did not
isolate the expensive body shape further; under the stricter no-repeat-shape
reading they should have been skipped/split. Both timed out and carry no credit.
No cap, timeout, function name or verifier verdict was changed to obtain a pass.

L042 attempted an importer before its NCO_Outer dependency was green. It
failed immediately; NCO_Search was made independent (Aeneas only), and the
actual dependency compiled L043. Failed-source introspection and draft errors
are retained, excluded from accepted source/axioms. L059 is the final failed
composition draft and was moved to NCO_AtCompose.failed.lean.txt.

Auxiliary *summary.log trailing blank lines were normalized for diff hygiene.
Canonical stdout.log/time.log/receipt.json files are unchanged.
