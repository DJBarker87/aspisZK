# Shared binary multiproof prerequisites, 2026-10-21

Branch `codex/cx-oracle-multi-20261021`, base `0f6232e31`.
This is additive prerequisite work. No final-soundness endpoint, existing
Lean module, S-cone candidate or M10 instrumentation file is changed. No
premise removal is claimed; the endpoint signature diff is empty. A port
still requires the user's approval.

## Execution model and deployed format

The source uses six shared proofs, not three independent 22-leaf proofs:
C1/C2/folded for queries 0..10, then C1/C2/folded for queries 10..22.
`candidate.rs::batch_tree` hashes every source opening before merging equal
indices (and checking equal leaf digests). `multiproof.rs::verify_in_place`
hashes each occupied parent once, using supplied sibling digests as values.
All trees have depth 18; folded indices are `u/4`, so their domain occupies
only 2^16 leaves inside the padded tree. Compact QM31 expansion preserves
the logical transcript bytes. Fixed length is 57,607 bytes, including six
zero-padded authentication slots with capacities
`[146,146,128,172,172,150]`, totaling 914 supplied digests.

`OracleDecisionMultiTree` gives an executable oracle program for shared
subtrees and root comparisons. `OracleDecisionMultiBuild.build` recomputes
occupied branches from public indices and supplies values for unoccupied
subtrees. `build_minimal` proves that every recomputed parent has an opened
descendant; `occupied_zero` identifies the opened positions. No independently
supplied parent-hash schedule is trusted.

Important boundary: the mathematical program traverses shared nodes in
postorder. Rust traverses levels and hashes source leaves before merging.
The duplicate-call allowance and address grammar are explicit, but a full
Rust/Lean order-and-parser refinement is not proved here. Arbitrary extra
frame inputs in the primitive model do not constitute a checked checkpoint
ABI implementation. This is a model prerequisite, not source refinement or
a new soundness theorem.

## Issued calls

For one nonempty binary shared subtree with D opened leaves and S supplied
sibling nodes, `parents + 1 = S + D` (`binary_count`). For six trees, let S
and D denote the sums and let X=66−D be duplicate source leaf hashes.
The terminal count is exactly

`6 checkpoint reads + X + D + (S + D − 6) = 66 + S + D`.

Including the sharp 115-call transcript allowance,

`B_V_multi(S,D) = 115 + 6 + 66 + (S + D − 6)`.

The checked slot capacities give S≤914 and D≤66, hence **B_V_multi≤1161**
for every admitted query set. The original constant is retained. Supplied
siblings and root comparisons issue no additional queries. Malformed
sampler constructors are covered by the upper bound; equality uses the
existing constructor-valid schedule condition, not Merkle acceptance.

`OracleDecisionMultiProfile` proves a sparse maximum by symbolic padding and
four-level skeleton counts, rather than evaluating a 2^18-leaf tree. C1/C2
parent counts are 155 (batch A) and 183 (batch B); folded counts are 137 and
161. Thus `2*155+137+2*183+161=974`. This is an attained **model** profile.
It does not certify a concrete frozen Rust proof or its query-sampler image.

## Shared-path leaf recovery

`OracleDecisionMultiRecovery.shared_path` constructs a leaf-to-root path for
each `OpenedAt` position. Its full trace is contained in the shared program's
inputs: siblings shared with another opening are obtained from that subtree,
not independently rehashed. Acceptance implies all computed roots equal their
committed roots. `accepted_leaf_recovery` then applies the existing generic
depth collision-free cut theorem. The public position is retained as the
reversed root-to-leaf route; this is not recovery from a root without an index.

Width, 32-byte salt, root-frame parsing, the run's first-read bound and the
existing five-reader collision exclusion remain explicit. Successful path
recomputation and path-read containment are derived, not assumed. The theorem
covers occupied leaves of the shared tree.
`OracleDecisionMultiCompiledRecovery.accepted_leaf_recovery` establishes the
same result in the annotation compiler’s own recorded log, under that log’s
first-read and collision hypotheses. Source duplicate-index checks,
matching of parser openings to those positions, and source-order refinement
remain part of the source join described above; ignoring an inconsistent
duplicate is not claimed to be safe.

## Recorded log and M10

`OracleDecisionMultiAccounting` proves, for the same annotation compiler,

`recorded length = prover length + 2 * full-verifier length ≤ Q + 2322`.

The compiler replays the **whole** oracle decision. Distinct first reads still
cost at most `Q+1161`, but replayed entries occupy log space. The old
`Q+1161` size premise does not follow from a first-read bound.
`full_profile_log` proves exact length 2322 at Q=0 on a constructor-valid
maximum shared profile. The profile itself accepts under the zero oracle,
which resource accounting is required to cover.

The current ledger restricts all four accounting fields to accepted runs
with `run.1.length ≤ Q+1161`. One safe size reindex is
`Qledger := Q+1161`, so its envelope becomes `Q+2322`. This is a proved size
identity, **not** a proof of `LedgerRefinement e p (Q+1161)` from
`LedgerRefinement e p Q`. That implication would strengthen the domain of
all resource obligations and is not asserted. A ledger family already
adequate uniformly in Q can instead be instantiated at the shifted parameter.
For a polynomial `C*(Q+1161)^d`, the shift costs at most a factor `2^d`
with unchanged degree; `ledger_polynomial` proves the bound. Cubic costs may
use 8C, quartic costs 16C, once the corresponding adequacy is supplied.

Read-only coordination: M10 pass 6 was inspected at `49a4c1878`, including
`M10-INSTR6-20261021.md`. Its `RawExtractorCostComposedBin.LedgerRefinement`
still uses Q+1161. The pass's fixed cubic numerical family is separate from
implementation/heap/bit adequacy. No concurrent worker file is changed, and
no M10 implementation premise is claimed discharged here.

## Decoder starts: the zero rule is false for the current byte grammar

`OracleDecisionMultiDecoderFacts.node_absorb` proves an equality of literal
65-byte encodings:

`0x12 || zeroDigest || (0xa1 :: 31 zero bytes)`

is also

`bytes(endpoint) || [0, label(1)] || 31 zero bytes`,

where endpoint begins with 0x12 and otherwise contains zeros. The current
selected message codec admits the 31-byte message: it checks a size bound,
not the frozen row-one record shape. A finite supporting table contains
three earlier initial/row-zero/advance cells plus a cached C2 leaf with the
actual 128-byte packed width, tag 0xf1 and 32-byte salt.

The symbolic singleton-fiber and one-step walk lemmas establish actual public
selection and ordinary semantic decoding, without reducing `Finset.univ` on
the padded address type. `recognized_node` proves that the existing
`RecordedBinaryExperimentBin.dec` recognises the parent input; `node_fresh`
proves it is fresh. `terminal_start_count` gives **exactly one** recognised
fresh start for a minimal shared authentication terminal. No decoder-success
hypothesis is supplied to that theorem.

`OracleDecisionMultiDecoderDepth.concrete_depth18_count` pads this example
symbolically to depth 18 and proves the count is still exactly one for an
explicit `exampleHash`. `exampleHash_agrees` proves agreement with every
defined cell of the supporting table. The upper padding deliberately uses
a colliding oracle; this is not a zero-start counterexample restricted to
collision-free runs. The one-parent recognition fact does not require any
oracle-value assumption.

This is a byte-grammar/decision-kernel counterexample. It is not an accepted
57,607-byte frozen verifier run, and it is not a proof that the aggregate
Q+34 bound is false. A different charging argument might still establish that
aggregate bound. What fails is the proposed universal **zero terminal starts**
shortcut for the existing decoder; source-only first-byte separation does
not repair it. A row-aware decoder needs a new density/completion proof and
source/byte alignment, or the port must use another proved accounting bound.

The unconditional result for the current shared program is **Q+1080**:
34 sampler starts plus at most 1046 terminal calls. Compiler replay adds zero
fresh starts. This is a safe constant, not an exact worst-case start count.

## Constants and revised port estimate

No endpoint is ported, so the existing endpoint constants and signatures are
unchanged. These are the exact constants established for a potential port
using the current decoder and conservative accounting:

| Quantity | Established value / requirement |
|---|---|
| Proof storage | 57,607 bytes (source pin; parser correspondence remains) |
| Queries / binary depth / batches | 22 / 18 / 10+12 |
| Supplied siblings / distinct leaves | at most 914 / at most 66 |
| Parent hashes / terminal calls | at most 974 / at most 1046 |
| Transcript calls / full verifier B_V | at most 115 / at most 1161 |
| Original and compiled distinct first reads | at most Q+1161 |
| Compiled recognised decoder starts | at most Q+1080 (safe) |
| Recorded log entries | at most Q+2322 |
| Ledger parameter preserving the old size shape | Qledger=Q+1161 |
| Per-start error | 15/2^109 |
| Collision allowance | κ(Q+1161)=6*(Q+1161)^2/2^256 |
| Remaining additive errors | 2^-126 and 2^-454 |

`OracleDecisionMultiNumeric.safe_range` proves that the resulting scalar
upper bound is at most `(Q+1)*2^-100` for

`32 ≤ Q ≤ 14777960484892959601791002642008314224629686649`.

The upper endpoint is the original Qmax minus 31. Both neighbouring integer
failures are checked; the conservative envelope also fails at Q=0. These
are scalar facts, not a new soundness theorem. If a new zero-start/charging
proof retains 34, the unchanged B_V=1161 also retains the original numeric
range and collision constant; this packet does not assume that proof.

The earlier carrier estimate remains 70–95 modules / 180–280 declarations.
Budget a further 5–15 modules / 15–40 declarations if a new row-aware decoder
is chosen: approximately **75–110 modules / 195–320 declarations** overall.
This is a source-inspection estimate, not measured labour. The call-count
risk is resolved at the shared model level; the decoder and ledger-domain
issues remain design gates. Parsing the real compact openings, rejecting
malformed schedules, source duplicate checks, chronological traversal,
checkpoint framing, checked opening/word alignment, sampler-prefix transport,
and Rust/frozen/caller joins remain. The port remains unapproved.

## Verification and receipts

All 13 final modules pass Lean 4.32.0 with `-j1 -M4400 -DElab.async=false`,
private object overlays, the shared local lock and one Lean process at a
time. All 81 final theorem audits use subsets of
`{propext, Classical.choice, Quot.sound}`. There are no proof holes, custom
axioms, native decision procedures or new resource-limit options.

Receipts are in `evidence/oracle-multi-20261021/`. Every attempt records its
exact target/argv, source revision and SHA256 snapshot, direct-import object
hashes/fingerprint, exit, wall time, peak RSS, swaps, full axiom lines and
errors. `source-pins.json` records the Rust files inspected; it is not a
refinement certificate. `signature-audit.json` records unchanged R19 and
headline endpoint hashes and empty signature diffs.

There were 34 actual compilations: 15 successful (including two superseded
checkpoints), 17 exit-1 attempts and two signal-6 attempts. Decoder attempts
2, 3 and 5 reported kernel memory exceptions; attempts 6 and 7 hit the fixed
interpreter cap. These were replaced by separate symbolic decoder-lift,
singleton-fiber, one-step-walk and concrete-consumer modules; no cap was
raised and no unchanged failing source was rerun. Attempt 7 also rejected an
irreducibility attribute on an abbreviation; that attribute was removed.
The final decoder check peaks at 4,578,476,032 bytes, below 4.4 GiB, with zero
swap. The large-profile heartbeat failures were replaced by symbolic count
and acceptance lemmas, not larger limits. Other failures were local
elaboration, namespace, rewrite and arithmetic fixes. All failing snapshots
and diagnostics remain in the packet; only the final green sources are
accepted.

The first accounting launch captured its dependency inventory while the
builder was still queued, so its Build object hash was missing. It is a
superseded checkpoint, not accepted dependency evidence. The final accounting
source adds the exact verifier/log theorems and has a complete pinned import
inventory. No shared object directory was overwritten.

`audit.py` validates every snapshot/receipt, final source/green receipt,
current direct-import hash, complete theorem/axiom-audit coverage and that no
pre-existing Lean module changed. The manifest and audit are focused evidence
checks, not an unchanged full Lean replay. No package-wide, certificate,
Aeneas, SBF or runtime regression was run: those artifacts did not change.
This packet is not a fresh coherent frozen release build (D63).

| Module (`OracleDecisionMulti` prefix) | Attempt | Exit | Wall seconds | Peak RSS bytes | Swaps | Audits |
|---|---:|---:|---:|---:|---:|---:|
| Accounting | 2 | 0 | 6.705 | 3629285376 | 0 | 7 |
| Build | 2 | 0 | 22.988 | 3542466560 | 0 | 5 |
| CompiledRecovery | 2 | 0 | 12.952 | 3605397504 | 0 | 2 |
| Decoder | 8 | 0 | 31.292 | 4578476032 | 0 | 6 |
| DecoderDepth | 2 | 0 | 6.500 | 3632594944 | 0 | 8 |
| DecoderFacts | 1 | 0 | 6.095 | 3598401536 | 0 | 7 |
| DecoderLift | 3 | 0 | 9.153 | 3618177024 | 0 | 4 |
| DecoderWalks | 1 | 0 | 5.123 | 3613818880 | 0 | 1 |
| Numeric | 1 | 0 | 8.193 | 3640836096 | 0 | 6 |
| Profile | 3 | 0 | 4.230 | 3616735232 | 0 | 10 |
| Recovery | 3 | 0 | 15.164 | 3628761088 | 0 | 11 |
| Summary | 4 | 0 | 7.396 | 3624632320 | 0 | 4 |
| Tree | 2 | 0 | 5.100 | 3649142784 | 0 | 10 |
