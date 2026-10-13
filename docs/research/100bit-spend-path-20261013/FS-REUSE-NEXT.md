# FS reuse inventory for the R1 twofold schedule

Source inventory only. No theorem was instantiated or compiled for the 33-round schedule. This note makes no claim about whether any new premises are true or whether the spend path meets its security target.

Repository snapshot: `/Users/dominic/ZK/.worktrees/100bit-spend-path`, branch `codex/100bit-spend-path-20261013`, HEAD `65d5de037cf0acae9b15545ef88d9d5bb6800e0a`. The Lean sources below are frozen research snapshots in this checkout; hashes are SHA-256 of the listed files.

## Generic interface already supports a variable round count

`docs/research/v8-r0-sem-proof-20261008/lean/R0P/MaskFiatShamir.lean` lines 14–20 establish local `prQ := combinedProtocolAt B p (n + 2) msg decode`. Lines 37–45 give `combinedInj` assuming `hrRounds : p.rounds = n + 2`, with a first-read count bound and `Inj3` result for `combinedDec p (n + 2) x`. Lines 49–65 give `combined_fiat_shamir_of_obligations`: its conclusion charges `maxErr rb.ε (n + 2)` and takes explicit `hD1`, `hD2`, `hD3`, `hQ`, plus the chain-read bridges. This is the direct round-count-parametric entry point; instantiating it at 33 would still require the corresponding new protocol/decoder and all obligations.

The generic FS2 obligations are defined in `docs/research/v8-fs-generic-20261006/lean/FS2/Statement.lean`:

- `D1` lines 171–172: `∀ x T, extract x T = none → doomed (emptyPrefix x) T`.
- `D2` lines 177–181: for each `i`, prefix `P`, message `m`, tables `T' T`, when `P.round = i`, `i < pr.r`, and `P` is doomed at `T'`, the sampler’s independent mean of extensions that are not doomed at `T` is at most `ε i`.
- `D3` lines 198–201: a doomed full transcript at round `pr.r` implies verifier rejection.
- `ChainDensity` lines 192–196 is the bridge derived from D2: every decoded completing sampler’s bad-output mass is at most `maxErr rb.ε pr.r`.
- `Inj` lines 220–234 is the collision-exception plus decoded-completing-sampler law expected by the theorem.

The generic duplex decoder has a useful completeness law. In `docs/research/v8-fs-generic-20261006/lean/FS2/DuplexWalk.lean` lines 103–120, `completeRounds_recs` proves that if every completion squeeze lookup agrees with the oracle, the completed records equal the actual transcript rounds. `DuplexDecode.lean` lines 151–160 defines `completeRounds`/`completePrefix`; lines 228–243 constructs `decode` with fuel `p.rounds`, returning a completing sampler, and `protocol` at 245–253 uses `p.rounds` as its protocol round count. `DuplexDecodes.lean` lines 140–214 gives `decodesSpec` for this decoder under the generic first-read bound; lines 323–335 plug D1/D2/D3 and that spec into the duplex FS bound. These interfaces are not intrinsically fixed at 32.

## Closed old masked instance and fixed boundaries

Pinned `MaskFiatShamir.lean` SHA-256: `a0644aa758d626a05753e66d50a8eb33d5fdaafb3ba655e0bfcdaf9a1ef2a6e2`.

- Lines 73–100 are literal 31- and 32-round `Inj3` aliases. The latter calls the generic wrapper with `n = 30`; this is an adapter, not a general limitation.
- Lines 113–141 close the old masked theorem at `hr32 : p.rounds = 32`. It assembles `combinedD1Z`, `combinedProtocolZ_D2`, and `d3Z`, with semantic challenges at `i < 25`, circle challenges at 25 and 26, then opening challenges at `27 + j.val` for `j : Fin 4`. The bound uses `maxErr combinedD2BudgetZ 32`.
- Lines 47–65 show the D1/D2/D3 obligations remain explicit in the round-generic theorem; the closed theorem discharges them only for the old schedule.

Pinned `MaskD2Instance.lean` SHA-256: `0ad9479ac29e8795f02f420c7b921d4bda14edd9ae4ed29db114ff5139d07b50`. `combinedProtocolZ_D2` lines 13–22 states the old D2 result. Lines 23–27 narrow `i < 32`; lines 28–59 split at literal boundaries 25, 27, and 31, with special cases for 25, 26, opening indices 27–30, and terminal index 31. The sub-bound applications are named (`semantic_rowZ_D2`, `circle_row25_D2`, `circle_row26_D2`, `opening_fieldZ_D2`, `opening_q22Z_D2`). The final index and case split must be inventoried against the R1 row layout before reuse; they do not generalize by merely changing `hr32`.

Pinned `MaskD3Glue.lean` SHA-256: `7270ca471ad9d35a3db8ab279753df826f2d519bf626115fd4d39d825a303dab`.

- Lines 115–153 prove old `d3Z`. Its final verifier transcript/message are fixed at 32 (lines 133–135), its first opening row is fixed at 27 (141–145), and its head-nonzero bridge is derived via `combined_chal27` and `gamma_ne_zero`.
- Lines 17–104 contain `accepted_no_hit_extractedZ`; the proof uses a 25-round semantic prefix and two explicit pre-opening circle challenges. These are schedule-specific extraction bridges and need review if R1 moves the schedule boundary.

## Literal five-round opening path

Pinned `SemD3Glue.lean` SHA-256: `60830349937666ec050499c10bdb51e5c17811a949edd494f9205f0ee45ad852`.

- Lines 531–549 define `openingParams`: its labels shift by `26 + j`, but `rounds := 5` is literal at line 547.
- Lines 557–568 define `combinedSampler`: indices below 30 use the one-block sampler; the tail enters an eight-pair `DQ.chainS` at line 568.
- Lines 963–980 define `combinedProtocol` with literal `r := 31`; lines 995–1007 bridge the opening head at global round 26.
- Lines 1034–1058 derive the global-round-26 opening challenge; lines 1060–1100 prove generic-field D3 for this 31-round mixed protocol, using that fixed round and opening index.

The masked extensions in `MaskD3Glue.lean` and `MaskFiatShamir.lean` use shifted old boundaries (opening head 27, final index 32). R1’s twofold 33-round schedule therefore intersects fixed-layout assumptions in multiple layers: challenge partitioning/D2, transcript completion and decoder views, D3 verifier final index and opening head, and the five-round opening subprotocol. The generic FS2 theorem and `n + 2` wrapper are candidate reuse points; the fixed bridges need line-by-line compatibility review after R1’s round map is settled.

## File pins

| File | SHA-256 |
|---|---|
| `docs/research/v8-r0-sem-proof-20261008/lean/R0P/MaskFiatShamir.lean` | `a0644aa758d626a05753e66d50a8eb33d5fdaafb3ba655e0bfcdaf9a1ef2a6e2` |
| `docs/research/v8-r0-sem-proof-20261008/lean/R0P/MaskD2Instance.lean` | `0ad9479ac29e8795f02f420c7b921d4bda14edd9ae4ed29db114ff5139d07b50` |
| `docs/research/v8-r0-sem-proof-20261008/lean/R0P/MaskD3Glue.lean` | `7270ca471ad9d35a3db8ab279753df826f2d519bf626115fd4d39d825a303dab` |
| `docs/research/v8-r0-sem-proof-20261008/lean/R0P/SemD3Glue.lean` | `60830349937666ec050499c10bdb51e5c17811a949edd494f9205f0ee45ad852` |
| `docs/research/v8-fs-generic-20261006/lean/FS2/Statement.lean` | `e472de7d36479495d55e10436635344bf7d2187f223ae73bd0b1db3c78718b36` |
| `docs/research/v8-fs-generic-20261006/lean/FS2/DuplexWalk.lean` | `206f5cf79a51b4254d9bf60a70ba85c1b7c188f00e1bbe49445a6319681c875c` |
| `docs/research/v8-fs-generic-20261006/lean/FS2/DuplexDecode.lean` | `9aa6e9a61007ad3ec6b6dd23cf5cb6edf466306032d9e28de9ce04dddf673f3c` |
| `docs/research/v8-fs-generic-20261006/lean/FS2/DuplexDecodes.lean` | `e0bc8715cb65768fcfaa6dfa1a16fc417693797c0ff0478cc7aba596d169fe93` |
