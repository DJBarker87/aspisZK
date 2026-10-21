# Oracle port continuation 4: stored proof versus transcript rows

Draft on `codex/cx-oracle-port-draft-20261021`; no deployment or merge.
This report supersedes continuation 3's capacity-only justification for a
separate carrier. Exact frozen row contents, rather than their capacity, are
the reason a carrier is required.

## Stage 1: byte map

`evidence/oracle-port-draft-20261021/OraclePortLayoutC4.json` gives every
half-open range, row framing, opening field and node slot, with source pins.
The source is `compact.rs`, `candidate.rs`, `r1_wire.rs` and `verifier.rs`.
The 1,233-case `j1_terminal_codec_trace.rs` gate covers Pool statement codecs;
it does not encode or test compact proof opening coverage.

| Stored range | Fiat–Shamir row / other use |
|---|---|
| 0–16 | Magic, S2 and zero header tail; checked, not a row payload |
| 16–48 | C1 root in public/root initialization |
| 48–7031 | 27 framed semantic records, rows 0–26; compact QM31 payloads on rows 14–26 expand from 16 to 32 bytes |
| 7031–7495 | 29 compact y1 values, expanded to 928 bytes at row 27 |
| 7495–7527 | Inactive value, row 28 |
| 7527–7751 | First polynomial, row 29 |
| 7751–8007 | Folded root plus second polynomial, row 30 |
| 8007–10055 | 64 final values, row 31 |
| no stored bytes | Empty row 32 payload |
| 10055–28359 | 22 openings of 832 bytes; read by query arithmetic and salted leaf hashing; never a Fiat–Shamir row payload |
| 28359–57607 | Six shared multiproof slots, capacities 146/146/128/172/172/150; supplied nodes read by binary Merkle hashing; zero padding checked |

Inside each opening: C1 values 0–480, C2 values 480–608, salts 608–640
and 640–672, folded values 672–800, folded salt 800–832. These leaf/node
oracle calls are distinct from the state-threading transcript absorb calls.
The checkpoint separately hashes the complete stored proof, including all
slot padding; being hashed there does not put its bytes into a row.

33 × 3717 = 122661 is only the type capacity ceiling. The logical framed
records total 17311 bytes (including the empty semantic row 0 record which
is implicit in the model's initial-message handling); the 32-byte C1 root
is separate. The semantic region including that root is 13831 bytes.
The omitted suffix is 47552 bytes. Arbitrary bounded model payloads *could*
encode those bytes, but the exact frozen row projection does not. Appending
those bytes to reached rows would change the absorbed bytes/challenges and
would fail exact frozen row parsing. No claim is made that the permissive
bounded-message type itself rules out such an alternative protocol.

`OraclePortRowStorageC4.rows_ignore_suffix` proves all projected rows ignore
any suffix beyond offset 10055. `exact_length_ambiguity` constructs two
57607-byte carriers with equal projected rows and a different opening byte.
It is a projection counterexample, not an accepted-proof construction.
The static audit also constructs two canonical, well-framed zero-field
layouts differing only in a C1 salt; hashes are recorded, bytes not committed.
No parser reading concatenated frozen rows can uniquely recover that salt.

Focused attempt 1 failed because `prefix` is a Lean reserved keyword;
attempt 2 renames it and passes. All three audits use standard axioms,
peak RSS 4258463744 bytes, zero swaps. Full per-attempt section 6 fields
are in the manifest and receipt directories.

## Subsequent stages

Separate stored-proof experiment/compiler and the resumed stage (c) audit
are recorded below as they are completed.

## Stage 2: separate carrier, parser and compiler

`OraclePortStoredExperimentC4.Input` adds one field, `stored : Bytes`, to the
public/proof pair. The prover supplies it in its oracle program output; it
is not fixed after observing the oracle and then smuggled into a supposedly
fixed old decision. The new decision type is `Bytes → Decision` and the
verifier chooses `d i.stored` from the same input. The sampler protocol and
3717-byte message bound remain unchanged. The original experiment retains
that input. The annotation compiler records the full original run, enriches
only literal word metadata, and retains stored bytes byte-for-byte.

Eight compiler/accounting theorems pass. They prove exact program replay,
public/stored/acceptance equality, unchanged distinct first reads, and
recorded log length ≤ Q+2322 under the all-input per-stored-proof budget.
There is no fixed-carrier or prover-independence assumption. This is an
interface repair, not a deletion-only specialization of an old signature.

`OraclePortStoredParserC4.parseReached` parses `stored`, then checks
`Aligned` against the erased prefix. `parsed` proves exact wire identity,
parser success and alignment; `parse_of_parts` composes the header, canonical
scan, semantic decoder and alignment checks. The latter is conditional,
not a nonvacuity witness. `kernel` reads queries from the reached row 31,
checks padding and executes the six shared slots. Its all-input decision
budget is ≤1046 (six-slot work itself ≤1040), with no impossible terminal
proof payload. `kernel_accepted` exposes actual parser/query/padding/tree
results. It does not conclude typed arithmetic acceptance.

The successful compiler/parser attempts are 2 and 2. Compiler attempt 1
used the reserved structure-field name `public`; parser attempt 1 omitted
Option monad simplification and used pre-case equations after dependent
case splitting. Changed proofs fix these local elaborations. Successful
reports use standard axioms, zero swaps; exact resource fields are retained.

Pool impact: the checkpoint must retain the *same* `stored` argument across
TX1/TX2, alongside the existing saved-ten accumulator and prepared fields.
Its existing proof hash already binds every stored byte, including nodes
and padding. A hash cannot reconstruct those bytes; TX2 needs the retained
proof account/slice, not only the digest. `Input.stored` must therefore be
fed from the same Pool proof-account range (688..58295 in the adapter), with
exact byte identity across resume. Compiler recovery consumes the projected
legacy `RunView`, while the experiment retains the larger input. Existing
`OraclePortPool.poolTx2` and `CallerReachability` mention an old fixed
`Decision`/`Prover`; they cannot simply be instantiated with this new
prover-dependent carrier. A new caller identity must target the projected
new recorded run and carry stored-byte identity. Frozen proof-account ABI
and checkpoint field encodings do not need to change. The logical
finite-support codec can retain the larger checkpoint without claiming a
physical ABI implementation. No runtime or shipped source was edited.

## Stage 3: positive parser witness and Pool packet

`OraclePortHonestRowsC4` proves a generic semantic encoder/parser roundtrip.
Each row has the expected tag and length, with compact zero-field payloads.
Canonicality of any divisible-by-four zero buffer is proved by a generic
fold lemma; no 57,607-byte list is normalized in the kernel.
`OraclePortHonestStoredC4.wire` is an explicit 57607-byte header/root/semantic
encoding plus zero field/opening/node suffix. `parse_honest` proves successful
strict parsing, and `parser_nonvacuous` proves parser inhabitation. This is
an honest *layout*, not a valid spend or a Merkle-accepted execution.
The nonvacuity theorem is unconditional; header, scan and semantic success
are proved rather than given as hypotheses. Alignment to a reached public
transcript and full-verifier acceptance remain different obligations.

`OraclePortStoredPoolC4` adds `stored` to the logical raw/saved-ten packet.
Preparation records the prover's calls before projecting its public/proof
pair; these calls remain in the commitment-cut log. `stage1_stored` and
`resume_stored` prove exact carrier identity across the handoff;
`persisted_output` proves lossless storage with the existing symbolic
finite-support codec. `resume_matching` retains the existing saved-ten /
resumed-twelve matching law. None of these claims physical ABI encoding or
the complete resumed observation equals the new recorded experiment.

Honest rows attempt 1 failed from ambiguous `Byte` and an unfolded size
abbreviation; attempt 2 passes. Honest stored attempts 1–2 had small
elaboration errors and a recursion-limit failure: default simp tried to
expand long zero lists. Attempt 3 replaces that with symbolic slices and
bounded 16-byte header reduction, and passes. No limits were raised.
Pool attempt 1 had a dependent-case equation mismatch; attempt 2 passes.
