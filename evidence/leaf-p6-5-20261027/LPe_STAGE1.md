# Frozen dependency replay

Rule (c) completed: all eleven LPb passing checks now replayed under the
frozen graph: K001 covers five fresh Dot/rejection checks; K004 covers scalar,
wide and scalar-frame serializers; K005 six-wide serializers; K006 selected
field with arbitrary surrounding bytes; K007 zero-wide 29-push identity.
Every graph matches all 441 package tuples and every resolved edge. Every
active Cargo.lock before/after equals the frozen SHA256 5782e6a3…22ef.

K002: type-check error, new Ordered dictionary needed Copy; corrected source.
K003: combined serializer harness timed out at 90s; replaced by K004–006,
smaller independent harnesses. No unchanged timeout rerun or cap increase.

496-file scratch inventory found TWO missing inherited files: RealR1_client.rs
and RealR1_client_tests.rs. The former is guarded by r1p-check, absent from the
selected features (default, optimized-terminal, private-leaf-salts, program-build);
the latter is its test module. Neither is selected by these Kani runs. Restored
both exact frozen bytes before the next native stage. Other 494 native files
match the frozen release, except the explicit cfg(kani) module inclusion.
The omission receipt is retained; no omitted body result is claimed.

All results retain the LPb domains: zero-wide identity is restricted, fresh
Dot return/error frames are not general post-state or finalization laws.
Both full P6 leaves and actual-top implementation premises remain OPEN.
No Lean theorem or native-result axiom was introduced.
