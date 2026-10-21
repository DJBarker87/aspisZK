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
