# Binary-node / wire-length separation (2026-10-20)

Branch `codex/cx-wire-len-20261020`; parent `f2c084bc8f51c02f4c58b6d0a4e3dd450867e1f5`.
Existing Lean modules and Rust sources are unchanged. New modules only.

## Status and obstruction

The requested single fixed length for `SemanticPublicWire` is false. Its
transfer encoding is 1455 bytes and its withdrawal encoding is 1427 bytes.
`BinWirePublicLengths.variants_differ` proves this for every common payload,
recipient and amount; this is a counterexample family, not an empirical check.
The valid replacement is a variant-specific length theorem and exclusion of
65 for both variants. No deployed record class with length 31 or 65 was found.

## Encodings and record classes

All paths in the table are relative to the repository. These are logical
hash bytes, **not** compact stored bytes. `compact.rs:5` explains expansion
before hashing; `compact.rs:34` fixes logical y1 to 928 bytes and
`compact.rs:44` fixes final to 64 wide values. `candidate.rs:76` constructs
that logical View; `verifier.rs:71` consumes it. C1 is a 32-byte root in the
initializer (`r1_wire.rs:179`); C2 is the 32-byte row-2 payload; the folded
root is the first 32 bytes of row 30 (`verifier.rs:78`). No root moves rows.

| Rows / class | Raw payload | Framed record | Absorb hash input |
|---|---:|---:|---:|
| 0, 1, 3–13: empty, tag 0 | 0 | 5 | 39 |
| 2: C2 root, tag 1 | 32 | 37 | 71 |
| 14: mask sum, tag 3 | 32 | 37 | 71 |
| 15–24: 28 coefficients, tag 2 | 896 | 901 | 935 |
| 25: 87 claims + 29 extra values, tag 4 | 3712 | 3717 | 3751 |
| 26: 29 before-z1 values, tag 5 | 928 | 933 | 967 |
| 27: y1 / gamma | 928 | 932 | 966 |
| 28: inactive sum / kappa | 32 | 36 | 70 |
| 29: first fold, seven wide coefficients | 224 | 228 | 262 |
| 30: folded root + seven wide coefficients | 256 | 260 | 294 |
| 31: final 64 wide coefficients / queries | 2048 | 2052 | 2086 |
| 32: empty / rho | 0 | 4 | 38 |

Semantic framing is tag + LE32 length + payload (`r1_wire.rs:39`, `:63`,
`:81`); semantic absorb prepends state[32], 0, label (`r1_wire.rs:203`).
Thus the root/mask hash-input length is **71**. Opening framing is
LE32 length + payload (`transcript.rs:14`), so it lacks the semantic tag.
The opening caller is `verifier.rs:74`–`:84`; the exact lengths are also
`lean/OpeningRecordCodec.lean:38`–`:60`. Semantic codec constructors and row
validity are `lean/SemanticRecordCodec.lean:19`–`:46`; circle counts and
framing are `lean/CircleRecordCodec.lean:14`–`:28`.

Other transcript inputs: initializer 75 + semantic-public length = 1530 or
1502 (`lean/SemanticPublicCodecComplete.lean:43`,
`lean/RawTranscriptFrameBytes.lean:30`); opening reseed 29 + 1 + 32 = 62
(`transcript.rs:7`); squeeze / advance / query blocks 32 + 1 = 33
(`transcript.rs:17`, `:35`). Row-zero absorption is 39, and rho absorption
is 38. All classes exclude 65. The premise in
`R1Z/LayoutTagR1PBin.lean:81` specifically requires semantic **framed**
length != 31, opening **raw payload** length != 27, and final raw payload
length != 27; the table discharges precisely those conditions.

There are three public encodings, which must not be conflated:

* The semantic transcript serializes `Public.public_bytes`
  (`r1_semantic.rs:68`–`:70`;
  `crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs:2017`).
  `lean/SemanticPublicWire.lean:49` and
  `lean/SemanticPublicByteBinding.lean:43` fix transfer/withdrawal lengths to
  1455/1427. Option tags and the recipient/amount widths explain the 28-byte
  difference. `parsePublic` rejects trailing bytes through `decodeAfter`.
* ASF8 is the fixed **1880**-byte reconstructed statement. Its decoder checks
  exact length at `crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs:403`;
  the numeral is asserted at `:822`. Stage 1 decodes the public account then
  hashes those original account bytes (`programs/r1-cost-probe/src/r1_pool_adapter.rs:962`,
  `:981`; `programs/r1-cost-probe/src/lib.rs:49`). Stage 2 encodes the
  reconstructed statement and checks its length (`r1_pool_adapter.rs:1015`).
  These ASF8 bytes are the verbatim checkpoint public hash
  (`candidate.rs:212`, `verifier.rs:274`, `:297`; the job's old `:382` pin
  predates the source freeze).
* ASQ8 is the separate **320**-byte request. Exact decoder length guard and
  assertion: `pair_forest_terminal.rs:469`, `:824`. It is not the semantic
  transcript bytes or the checkpoint statement bytes. Both fixed envelope
  lengths exclude 65 as well.

The general byte hash API still accepts arbitrary public bytes, and the
counterexample `BinGrammar.unrestricted_public_overlap` remains valid.
The length guard is supplied by a concrete caller/encoding, never by that API.

## Proofs and compilation

New modules under `lean/` (each theorem has `#print axioms`):

* `BinWirePublicLengths`: parsed semantic lengths, node/public separation,
  the variant-length counterexample, and fixed-envelope separation.
* `BinWireRecordLengths`: the existing typed semantic, circle and opening
  codec lengths exclude the dangerous values; each resulting raw absorb
  input differs from every binary node input.
* `BinWireParsedLengths`: **successful extracted `parse_record`** implies
  record length in {5, 37, 901, 3717, 933}; consequently its literal absorb
  is separated. This consumes `ExtractedRecordFraming.parse_record_success`
  (`lean/ExtractedRecordFraming.lean:72`) and the actual extracted row table
  (`lean/ExtractedRowShape.lean:58`), rather than assuming parser validity.
* `BinWireEnvelopeLengths`: **successful extracted ASF8 decoding** implies
  length 1880 and hence node/public separation. It consumes
  `ExtractedTerminalDecoderSuccess.decode_success`
  (`lean/ExtractedTerminalDecoderSuccess.lean:81`). The numeral does not
  remain an added hypothesis in this theorem.

New privacy module:
`docs/research/v8-r0-zk-20261009/lean/R1Z/WireLengthsR1PBin.lean`.
Its concrete S2 `Wire` contains fixed-width payload slices, tagged semantic
frames, and 2048-byte final data. `transcriptNodeLengths` proves the landed
premise for `rest w`; `node_ne_concrete_transcript` applies the landed
`nodeBytes_ne_transcript` theorem. It is independent of field canonicality:
all byte contents of each correctly sized payload are covered. The carrier
uses the row-shape table above, not a hypothesis restating the desired
inequalities. No existing privacy dependency source or object was replaced;
the new module is an additional consumer of `LayoutTagR1PBin`.

Local receipts:
`evidence/wire-lengths-20261019/manifest.json`
(schema `focused-extractor-proof-packet-v1`), per-attempt `receipt.json`,
`lean.log`, `time.log`. Four final modules / 19 theorem audits passed with
Lean 4.32.0, `-j1 -M4400 -DElab.async=false`, shared mkdir lock and own
`/tmp/cx-wire-len-objects`. Standard axioms only; zero process swaps. Final local wall total 22.57 s;
peak RSS 3,479,142,400 bytes. `audit.json` matches all final source hashes
and checks all 24 successful theorem audits; no Lean replay was needed.
Historical failed attempts are retained: one elaboration repair in the
variant counterexample, stale/missing cache-path diagnostics for the parser,
and an explicit scalar-substitution repair in the row-table proof. No
memory-pressure failure or cap increase occurred. The parser dependency
repair installs symlinks only in this branch's own object directory to live
cached objects, leaving all shared caches untouched. A waiting-shell false
positive in the first process gate was interrupted before compilation; the
runner now checks the executable token, not text inside a waiting shell.

Env J evidence: `evidence/wire-lengths-20261019/j-attempts.jsonl` and `J/`.
Attempts are also appended to J's shared `evidence/attempts.jsonl`.
6250 failed only on addition reassociation; 6251 passed the privacy module
(all five theorem audits standard-only, 2.14 s, 3,363,780 KiB, zero swaps).
The failed source was snapshotted on J in the branch-named snapshot directory
before replacing this new module. Attempts 6252–6255 respectively requested
`FinalR1PBin`, `PrivacyR1PBin`, `PrivacyBoundR1PBin`, and
`R1J.PrivacySamplerSpendBin`: all exited 67 at the unchanged fingerprint
refusal, with no Lean run. No refusal was bypassed and no unchanged full
manifest was replayed. All J compile requests used the existing launcher,
-M7000, MemoryMax 7G, MemorySwapMax 0 and its reservation check/locks.

## Remaining boundary

The unrestricted literal message carrier is **not** a row-specific wire
validator: `lean/R1SelectedTranscriptParams.lean:21` only bounds length by
3717; `lean/LiteralTranscript.lean:54` checks constructor schedule, not
payload sizes. Therefore these theorems specialize typed encodings,
successful retained parser/decoder executions, and the concrete privacy
wire carrier. They do not claim every arbitrary `LiteralByteProtocol`
message or every arbitrary privacy `Rest` has safe lengths. Identification
of Rust prover/verifier executions with those encodings still belongs to
R-wire / the source simulation. The successful extracted-parser facts
advance that boundary but do not prove a whole transaction simulation.
ASQ8's 320-byte source guard is pinned above; this packet supplies no new
extraction of its decoder. The source freeze, ROM interpretation, global-log
embedding, account authentication and all other gap-map premises remain
unchanged. No Rust/SBF artifact changed, so runtime gates were not rerun.
