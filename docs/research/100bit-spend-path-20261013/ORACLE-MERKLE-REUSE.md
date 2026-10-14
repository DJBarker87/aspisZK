# Oracle-verifier and 32-byte Merkle reuse

The existing verifier and Merkle proofs now have two focused adaptations
needed by R1. They are generic model results; the concrete Rust terminal
checker, commitment-time reconstruction and full security theorem remain
open.

`OracleVerifier.verifier` retains the old FS2 sampler schedule and changes
only the terminal interface from a Boolean to an oracle program. Its exact
evaluation theorem states that the trace is the concatenation of all
sampler-chain traces followed by the terminal program's trace. Its output
is the terminal program's output. Separate lemmas include every sampler
read and every terminal read in that full trace. Specializing the terminal
program to `.done (decision prefix message)` is proved equal to the original
FS2 verifier as a program, not merely on accepting executions.

This supplies a suitable interface for modeling Merkle hash calls. The
previous `UnifiedFiatShamir` theorem still uses the old Boolean interface;
its experiment recovery and budget arguments have not been lifted to this
new verifier. Nor has an actual Merkle/checkpoint terminal program been
provided here.

`Merkle32Path` adapts the R549 proof with only the digest geometry and
namespace changed: 32 bytes per digest, 256 child-major bytes, and a
257-byte parent preimage including tag `0x18`. The complete slot-indexed
path and collision alternative are retained. Equal roots reached from
different leaf digests at the same position expose two distinct equal-hash
preimages in the two literal traces.

`Merkle32Leaf` reuses R552's fixed-width concatenation argument. The
selected salted leaf grammars are:

| Tree | Tag | Packed bytes | Salt bytes | Complete preimage bytes |
|---|---|---:|---:|---:|
| C1 | `0x71` | 480 | 32 | 514 |
| C2 | `0xf1` | 128 | 32 | 162 |
| Folded word | `0x72` | 128 | 32 | 162 |

Each preimage starts with `0x10 || tag`. The path theorem proves that two
same-root openings with the same full slot list either have identical
payloads and salts, or reveal a collision in their literal traces. It is
deterministic and does not assign a collision probability. It also does
not provide a second opening from a commitment-time table, prove tree
construction, identify the seven-sibling wire layout, or prove source
execution. Those obligations are recorded in
[the knowledge and oracle boundary](KNOWLEDGE-AND-ORACLE-BOUNDARY.md).

The three focused modules and one combined checkpoint passed on the NUC.
The checkpoint prints 22 audits, including the four leaf-length results,
and passed in 0.73 s at 1,794,772 KiB peak RSS with no swap. All successful
reports use only the standard Lean axioms or none. Exact final sources,
object hashes, resource receipts and historical attempt gaps are recorded
in [the evidence bundle](evidence/lean-oracle-merkle-20261014/README.md).
