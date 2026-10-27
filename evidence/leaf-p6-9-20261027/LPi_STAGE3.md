# Writer callers, powers, and ordered digest cuts

CM31 parent16 offsets0/8 and parent32 pass using the audited M31 byte stub
(K002–004). QM31 exact16 and parent32/48 contexts pass using the audited
CM31 stub (K005–010). The actual private put_k passes for arbitrary prefix
contents and EVERY length0..1720, exact16 bytes and universal selected-byte
frame (K012). Actual put passes for every prefix length0..1704 with the E
byte stub, exact32 bytes and universal frame (K013). Covers are reached.

LPi_SerializationFold.weights64 proves generic append-fold contents and the
712+64*16=1736 checksum-input length. It is a list induction paired with the
native put_k one-iteration caller check; the complete emitted checkpoint loop
association and one whole checkpoint execution are NOT inferred from it.

LPi_PowersSource.source proves total emitted powers for every length and
canonical x, including seven, with exact recursive natural-coordinate values
and canonical entries. LPi_PowersStep proves the actual one-step body;
LPi_PowersPrefix and PowersValue supply a prefix invariant and induction.
K014 attempted the corresponding copied native one-iteration body with an exact
natural E.mul stub. It timed out at90s; no pass is credited. Split K015 proves
the final write/return cut; K016 proves the continuing write/increment/frame
prefix and exact next-call operand position. Neither split proves the multiply
call continuation. No unchanged timeout replay or timeout/cap increase occurred.

K017 checks ONE native execution of the ordered three digest cuts with
nondeterministic32-byte answers: proof, public, labelled1736-byte body, followed
by exact32-byte checksum append and1768-byte result, all selected bytes and
final-byte cover. It uses3/5 proof/public preflight carriers. The body between
first two digests and checksum is an arbitrary serializer-cut pre-state with
those SAME answers installed at offsets16/48. It is not an actual whole native
checkpoint body execution. K018 separately tests physical57607/1880 carriers;
its receipt decides that stage. SHA is never unwound. The missing association
from actual checkpoint serialization to this cut remains OPEN regardless of
K018's result; no serializer output is assumed in the actual top theorem.

K001 and K011 were harness overlay/module-resolution compile failures. The job
removed inherited contracts and repaired its OWN scratch module path. A sync
quoting error launched no prover and was repaired in the job-owned script.
No reservation, launcher, monitor, shared object, shipped source or artifact
was changed. Full frozen inventory LPi_SOURCE_AUDIT.json checks498 files,
allowing only the two appended cfg(kani) harness registrations in scratch.

K018 PASS: arbitrary57607/1880 physical carriers, all769 checks and both covers pass,23.591s wall,1791788KiB RSS,swap0. It remains a joined cut, not the whole checkpoint caller.
