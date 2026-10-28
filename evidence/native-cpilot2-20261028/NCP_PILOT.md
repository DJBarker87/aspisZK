# NCP composition pilot

PILOT RESULT: pending. No native or headline credit yet.

Result-returning slice codecs and Vec output; U02 digest -> U03 afterstate/live/late -> U05 ASF8. Contracts and per-shape controls precede caller credit. Frozen Rust 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387; headline AspisR1.RPx_Deployed.deployed.

Budget: 70 Kani, 60 Lean; one admitted capped scope at a time. No inherited LPb stages credited.

Stage 1: Result/slice shape admitted in the tested one-byte context: K001 inverted ensures FAIL; K002 weak callee PASS; K003 real caller PASS; K004 weak stub caller FAIL; K005 modifies violation FAIL; K006 actual mutation PASS.

Vec shape NOT admitted: K007 inverted ensures FAIL (78.821s solver); K008 weak callee PASS; K009 real caller PASS; K010 stub caller CODEGEN ERROR: Result<Vec<u8>,u8> does not implement kani::Arbitrary. K011 unlisted slice mutation FAIL; K012 real mutation/Vec return PASS. K010 is not a passing negative control. No Option<fn> used.

The narrow body checks do not establish large-buffer or whole-codec contracts. No native row becomes unconditional from these controls.
