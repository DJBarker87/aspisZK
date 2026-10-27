# History stage 1: actual source zero gate and explicit collision event

Checked smallest changed modules in coherent SInt2 workspace, unchanged launchers,
6G/8G/swap0/tasks64 scopes, -j1 -M7000. Attempts001-010, no Kani. 001/004/007-009
are retained elaboration failures; no timeout/memory kill or unchanged rerun.

Hist_InitialZero.accepted_zero inverts the actual accepted extracted TX1 into its
own successful zero gate on the actual ORIGINAL checkpoint entry buffer. The
snapshot length is derived from this acceptance. no_reinitialize proves that
another accepted TX1 cannot target that buffer if its first byte is nonzero.
Hist_ZeroHead/ZeroReject prove immediate first-byte rejection symbolically,
without reducing a 1768-byte recurrence. Only standard axioms in passing outputs.

Hist_P2Prime.binding_or_collision derives the existing byte-binding proposition
from one consistent bounded log containing the four complete input reads, OR
returns the existing binary collision event. collision_bound records6*Q²/2^256
for that event on a fixed containing adaptive program with uniform whole-log Q.
No SHA/hash injectivity assumption. The source log/read provenance and concrete
history are not supplied by these local lemmas. Next stage charges four appended
audit reads to avoid introducing four source read-provenance assumptions.

Before: zero gate was irreducible and not exported by existing accepted guards;
P2Prime assumed byte identity under matching digests. After: actual writer gate
is derived, and P2Prime follows outside an EXPLICIT bounded collision event.
Quantifiers/carriers/acceptance are unchanged in these local source statements.
Ledger delta: removed NONE globally; added NONE to deployed endpoint. L094-L098,
L180 remain open pending the concrete runtime/accepted-pair composition. Local
source non-reinitialization does not establish a same-key/version save/load pair.
No full-release or jointly accepted cryptographic non-vacuity claim at this stage.
All commands/source hashes/dependency fingerprints/exit/wall/RSS/swap/axioms are
in numbered receipts; failed elaborations with sorryAx are excluded as evidence.
No shipped file or artifact changed; inherited pins in Hist_source-pins.json.
