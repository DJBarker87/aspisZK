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
