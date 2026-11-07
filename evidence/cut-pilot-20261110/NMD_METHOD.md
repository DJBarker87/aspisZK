# NMD native cut-point method pilot

Target not yet established. Baseline ledger23: 580 CLOSED / 0 QUALIFIED / 19 OPEN.

Stage 1 tests pinned Kani 0.67 contract fidelity before any actual-child substitution: Result<Box>, Ref, RefMut, ProgramResult and plain Result. Each shape requires inverted-ensures failure, real-body pass versus stub_verified failure for an unimplied assertion, and detection of a modifies violation. No verdict yet.

Route A is gated on all controls for the exact interface. Route B is attempted only for a failing shape and uses local records reachable through existing arguments with the remaining complete footprint havocked. Writable statics and zero-content parent carriers are forbidden. No binding template is validated yet.

Stages: controls; actual parse/marker/common contracts and arbitrary-content parent; conditional local-record route; informational newest-Kani K-3 check; Lean segment fold and combined audit. Only CLOSED or gated candidate children may compose. Root0/1880 remain TX2:241 caller clauses. No new trust rows.

Input repairs: sparse NLF/NLM evidence paths restored. K001 stopped in the owned gate before cargo-kani: verifier-only upload leaves program files frozen, while copied validator required program instrumentation. Validator now permits frozen program bytes or strips only the exact cfg(kani) instrumentation, then checks the same frozen hash; no source validation relaxed. K001 is conservatively charged; no shape verdict.

K002 stopped before cargo-kani on a missing unchanged manifest in the private corpus. Restored NLM_NATIVE_EXTRA_INPUTS with its pinned hashes (the same predecessor corpus extension); K002 is conservatively charged. K003 tests the unchanged shape after this input repair, not a retry of a timeout.

Initial plain Result controls: K003 positive PASS; K004 inverted ensures FAIL; K005 real body PASS; K006 stub_verified compiler rejection (missing Arbitrary for deployed Variant/Error); K007 empty-modifies violation FAIL. Proposed repair is exhaustive cfg(kani)-only Arbitrary implementations covering Variant S1/S2/D and all eight deployed Error arms. This adds no argument precondition and no runtime change. Re-test complete shape family with the original names after adding these constructors.

Initial Ref/RefMut controls: K021/K027 positive PASS; K022/K028 inverted ensures FAIL; K023/K029 real body PASS; K024/K030 stub_verified rejected (guard has no Arbitrary); K025/K031 modifies violation FAIL; K026/K032 KMX negative controls FAIL. Result<Box<u8>,Error> positive/real pass, inverted/modifies/copy controls fail, but stub_verified rejected pending the Error constructor test. These are compile-interface obstructions, not false passes. No timeout or memory kill occurred.

The initial controls are not a binding pattern. Direct Ref/RefMut contracts describe their RefCell borrow footprint with modifies(cell), but arbitrary guard generation is unsupported. No new guard Arbitrary impl is proposed (foreign trait/type and guard validity cannot be manufactured). Route B must keep a real constructor from the original cell and establish borrow/ownership separately.
