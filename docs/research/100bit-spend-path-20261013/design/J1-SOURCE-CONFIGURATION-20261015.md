# J1 source configuration inventory (2026-10-15)

This records selected source values and their locations at repository revision
`136b746805f3438507732622c9b4e50f36bf49f9`. It is a source inventory only;
it does not establish that the Lean byte models refine Rust execution.

## Selected build profile and version identifiers

The frozen split10 SBF build uses `pool-adapter,private-leaf-salts` and its
host `pool_gate` build uses `private-leaf-salts`; exact commands and features
are in `evidence/split10-v152-20261015/results/sbf-build.json` and
`driver-build-b.json`. The program dependency enables the probe's
`optimized-terminal` feature (`programs/r1-cost-probe/Cargo.toml:14–17`),
and the probe feature definitions are at
`crates/aspis-r1-cost-probe/Cargo.toml:8–26` (`private-leaf-salts` is an
empty feature at line 25). The build plan's “not runtime adopted” status is
historical. Later `evidence/split10-adoption-20261015/adoption.json` records
the three-file split10 adapter/driver adoption, measured ELF SHA-256
`5a91339444d14c2a9c63c9dbd22923003ebd79f63b76c97da175c2042aa62912`; its
README says this is research-branch adoption and no live program was
deployed. Separately, `evidence/shared-point-adoption-20261015/adoption.json`
records `weights.rs` arithmetic adoption and tested ELF
`7cf2fb3e7fe3a1237d508b0d3a2629d8cf1229ebf0e22c39ab236cd9a9dd255a`. These
are source/build status facts, not a security-release claim.

The identifiers `Variant::S2` and `VERSION_V4_S2` are separate namespaces of
meaning: `crates/aspis-r1-cost-probe/src/transport.rs:5–9` maps S1/S2/D to
variant tags `1/2/3` and assigns S2 two folds; the core proof envelope uses
version byte `4` for `VERSION_V4_S2`. The
constant is defined at `crates/aspis-core/src/proof.rs:57–65`, and the
candidate header writes it at
`crates/aspis-prover/src/circle_candidate.rs:1567–1577`. These facts
do not identify the probe's enum tag with the envelope version.

## Domains, row framing, and sampler calls

With `private-leaf-salts`, both semantic wire modules select the semantic
domain at `semantic_wire.rs:9–12` and `r1_wire.rs:9–12` as the ASCII string
`UNPROVED:R1:PRIVATE-SALTED:SEMANTIC:P3`; the opening `Transcript::new`
domain is `UNPROVED:R1:PRIVATE-SALTED:P3` at
`crates/aspis-r1-cost-probe/src/transcript.rs:7–12`. The semantic sampler's
absorb label is `0xa0 + row` (`semantic_wire.rs:133–147`); its
block then hashes the absorbed state with `[1]` for the returned block and
`[2]` for the next state. The transcript sampler additionally frames each
absorb as state, `[0, 0xa0 + row]`, 4-byte little-endian payload length, and
payload (`transcript.rs:14–21`). Its `queries` method absorbs its row payload
and performs eight block/advance pairs (`transcript.rs:35–45`).

The semantic transcript's initial state is
`hash([DOMAIN, [0], public_len_u32_le, public_bytes, c1_root])`
(`semantic_wire.rs:117–124`). The opening transcript's initial state is
`hash([DOMAIN, [variant.tag()], semantic_state])`
(`transcript.rs:7–12`).

The `semantic_wire::row_shape` layout (`semantic_wire.rs:38–48`) has these
P1 tags and payload widths:

| Rows | Record tag | Payload width |
|---|---:|---:|
| 0, 1, 3–13 | 0 | 0 bytes |
| 2 | 1 | 32 bytes |
| 14 | 3 | 32 bytes |
| 15–24 | 2 | 896 bytes (28 × 32) |
| 25 | 4 | 2,784 bytes (3 × 29 × 32) |
| 26 | 5 | 928 bytes (29 × 32) |

The separate `r1_wire::row_shape` layout (`r1_wire.rs:39–48`) agrees on all
rows except row 25, whose payload is `(CLAIMS + LANES) * 32 = 3,712` bytes.
The selected `host_semantic` imports `r1_wire` (`host_semantic.rs:3–5`), and
the verifier calls `r1_semantic::verify_observed` (`verifier.rs:341–349`);
that verifier decodes the extra 29 WideExact values beginning at index 87 of
row 25 (`r1_semantic.rs:102–123`). The 2,784-byte `semantic_wire` record is a
distinct layout and must not be conflated with that 3,712-byte row.

`semantic_wire::begin` (`semantic_wire.rs:260–283`) samples rows 0–14 in order
(lambda, chi, theta, ten `zc` values, mu, eta). Both semantic samplers label
rows 0–26 `0xa0` through `0xba` (`semantic_wire.rs:133–147`,
`r1_wire.rs:189–202`). In S2, later transcript labels rows 27–32 `0xbb`
through `0xc0`. The prover uses row 27 for gamma over `y1`, row 28 for kappa
over the inactive sum, row 29 for alpha0 over `c0`, row 30 for alpha1 over
`folded_root || c1`, row 31 for queries over the final message, and row 32
for rho over an empty payload (`prover.rs:190–229`). The verifier repeats
these uses from proof fields at `verifier.rs:86–99` and generates query and
opening checks at `verifier.rs:242–262`. Rows 30–32 depend on the two-fold
branch. Folded leaf construction is at `prover.rs:207–223`, and opening
serialization is at `prover.rs:239–255`; these are source-path facts.

## Merkle tags and private salts

Core Merkle tags are C1 `0x71` and C2 `0xf1`
(`crates/aspis-core/src/r0/merkle.rs:13–18`). In the S2 two-fold cost-probe
path the folded tree uses tag `0x72` (`prover.rs:213–218`). Each private leaf
salt is exactly 32 bytes (`crates/aspis-core/src/state_only_private_merkle.rs:9–35`).
`derive_private_salts` (`prover.rs:181–188`) creates one salt for every leaf index in
`0..FIBRE_COUNT`, separately for C1, C2, and (on the two-fold path) folded
leaves. `FIBRE_COUNT` is `1 << 18` (262,144;
`crates/aspis-core/src/r0/mod.rs:34`). Salt derivation
(`crates/aspis-prover/src/state_only_entropy.rs:568–585`) hashes, in order,
the salt-domain constant, attempt binding, mask nonce, one-byte tree tag,
4-byte little-endian leaf index, and private leaf-salt seed. Host salt buffers
are overwritten on drop.

For a queried opening, `verifier.rs:242–262` hashes C1's 480-byte payload with its
32-byte salt at query offsets 608–639, and C2's 128-byte payload with its
32-byte salt at offsets 640–671. The folded query contains 128 payload bytes
and a 32-byte salt immediately after it; the folded path uses index `u / 4`.
The prover constructs folded leaves as four encoded WideExact values (128
bytes) for the first `2^16` leaves and 128 zero bytes for the remaining
leaves, then salts each leaf under tag `0x72`.

## Comparison with the existing Lean byte models

`PublicInitFrame` (`lean/PublicInitFrame.lean:12–16`) pins the same P3 semantic-domain byte sequence. Its model
uses `domain ++ [0] ++ lengthBytes(pubBytes.length) ++ pubBytes ++ bytes(c1)`
for the initialization frame, and its row-zero absorb label is 160 (`0xa0`)
with a five-byte empty record. This is the model's explicit initialization
layout.

`OpeningReseedFrame` (`lean/OpeningReseedFrame.lean:12–18`) pins the distinct opening domain
`UNPROVED:R1:PRIVATE-SALTED:P3`; its frame is `domain ++ [tag] ++ bytes(s)`
and has length 62. The tag is a caller-supplied byte. That module does not
itself map rows 27–32 to tags or encode the Rust transcript's payload-length
framing. The source values above therefore provide a comparison inventory,
not a completed byte-level refinement.

## Source pins

All paths are relative to the repository root. SHA-256 values pin the exact
files inspected for this note.

| Source | SHA-256 |
|---|---|
| `tools/r1-split10-candidate/build-plan.json` | `c4b64732cd3613962672244bcc5b8a4c71c4d0bfcfabca56b531922c13d422ad` |
| `docs/research/100bit-spend-path-20261013/evidence/split10-v152-20261015/results/sbf-build.json` | `0fe479ecfb3d8238615e44283b363e974a114309ff6c5f656c3a6a696dbd4bc2` |
| `docs/research/100bit-spend-path-20261013/evidence/split10-v152-20261015/results/driver-build-b.json` | `dae37219ec9c04cb7ddd65468ec8f588c7c2c99e890cf5392af55fd393befdf8` |
| `programs/r1-cost-probe/src/lib.rs` (adoption pin) | `294546036e6cf8bb8dcc1f1f4a65c5e0887ac04593cdda801f58c75a284d582a` |
| `programs/r1-cost-probe/src/r1_pool_adapter.rs` (adoption pin) | `b2adab8610189a5031fc6f28a7cdeef12c01aa292423743cb4696aa3ee1590a4` |
| `tools/r1-cost-probe/src/bin/pool_gate.rs` (adoption pin) | `f8986a966a6b17340c84c8d6a3514eed061f25cba8f8d65433d458dc8f379406` |
| `crates/aspis-r1-cost-probe/src/weights.rs` (shared-point adoption pin) | `68c9087712ff6bfb08c7ed41a1281798466e6671800761c80f83126963262f63` |
| `crates/aspis-r1-cost-probe/Cargo.toml` | `5fafcd2572896d4ba35cb01304aa6ccde1d0b634804fedf22c3f74133cedf093` |
| `programs/r1-cost-probe/Cargo.toml` | `1208d93c95f3e4e769fd1ba48f71bbb031c4ddd33793f09f5cc6405fe9da71f1` |
| `crates/aspis-r1-cost-probe/src/transport.rs` | `34af7f077fdae8147ebd79a44e7acb38395ec440115109c8fbfc654cb2c1e8c7` |
| `crates/aspis-r1-cost-probe/src/transcript.rs` | `c91ffe824a55ff62659e8a194d2ea201032383e4e11e5f60625404a30c691ef6` |
| `crates/aspis-r1-cost-probe/src/semantic_wire.rs` | `58c671cee016246aa464a35ba443009813581e4a53bce37dd528d048009f2db7` |
| `crates/aspis-r1-cost-probe/src/r1_wire.rs` | `73f4b49dfae90be8a5cafd9d69eaf9ed06a01009f3daabc5627b42e6cf31c996` |
| `crates/aspis-r1-cost-probe/src/r1_semantic.rs` | `964f008a0841246fe3638ce2e492d12d18d78302565aa57f8c7df4d079579ce3` |
| `crates/aspis-r1-cost-probe/src/prover.rs` | `a7e20e5eb2fb706f2bdb51371466d4ee02c6fcabc67a427495a3b9276d9495fd` |
| `crates/aspis-r1-cost-probe/src/verifier.rs` | `2cab573be46ca69b5d82837e5221a9a499d3b6dc1f89b801e388b4e8b1fe01cd` |
| `crates/aspis-r1-cost-probe/src/host_commitment.rs` | `551c4f8a0df50e0b53ab7e79d4e71b8c6afe417043c55caa1c377da3388f890c` |
| `crates/aspis-r1-cost-probe/src/host_semantic.rs` | `113a367ae1e01d8fbd808ce3756b87040fd31ab359d94bad50b7c55c89c284bf` |
| `crates/aspis-core/src/proof.rs` | `a8e3b259da25d47a3d88b38ca838d57ab104476929fe5758b43d1a37c06306a0` |
| `crates/aspis-core/src/state_only_private_merkle.rs` | `f0edc31d07d30f5b19fcaf872fba18678d13d1ba5fac1199f1f4d2be74c74f9b` |
| `crates/aspis-core/src/r0/mod.rs` | `709f1d0d9be9d3ee74e2b63e13065f5a91c878ba77ed2d2e97a414fbbc646aca` |
| `crates/aspis-core/src/r0/merkle.rs` | `6df6b25bf5b29dd2744af9db645e3c5818fa9256a454f175db4b750919ce7224` |
| `crates/aspis-prover/src/state_only_entropy.rs` | `78ebbb3176daf23935243452992548ff9d877aaaf853d73e5ee46b60d8cb3ec0` |
| `docs/research/100bit-spend-path-20261013/evidence/split10-adoption-20261015/adoption.json` | `9264a843fe4b7fefc3ffd8bab7233d1789e69e3dce569d5faed2a23b7287e1fd` |
| `docs/research/100bit-spend-path-20261013/evidence/shared-point-adoption-20261015/adoption.json` | `bbf7a99af4189bdc682f1bac0330094249a6457ebcede711eb7b87987bbb49b8` |
| `docs/research/100bit-spend-path-20261013/evidence/split10-v152-20261015/bin/aspis_r1_cost_probe_program.so` | `5a91339444d14c2a9c63c9dbd22923003ebd79f63b76c97da175c2042aa62912` |
| `docs/research/100bit-spend-path-20261013/lean/PublicInitFrame.lean` | `756b529e3685c3341064b9970f5cebe71991b67eeeb5c6476a93934359f9a65e` |
| `docs/research/100bit-spend-path-20261013/lean/OpeningReseedFrame.lean` | `6624eb83586e4fff4b6e0f6686936baea1dca839c8174d81012bb64fc5fa032f` |
