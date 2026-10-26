# P1 priority and literal soundness rows

No row is removed. Inspect the literal types, not historical uses of the phrase
"Pool checkpoint". CP denotes verifier-owned1768 R1P2CKP2, ASC8 denotes Pool-owned192.

| Rows | Literal dependency | Does P1/ASC8 provenance discharge it? |
|---|---|---|
| L091/L092 | actual TX1 CP header/1768 output | No. Actual verifier child/write path only. |
| L093 | actual TX2 checked CP digest header | No. Reader source checks may consume reconstructed ASF8 separately. |
| L094 | CheckpointVersionBinding.savedAtCommit | No. Saved argument is native TX1 CP. Need committed actual CP copy/key. |
| L095 | CheckpointVersionBinding.loadedAtEntry | No. Need actual TX2 CP load at same key/history. |
| L096 | CheckpointVersionBinding.noInterveningWrite | No P1 success theorem required. Pool is foreign owner of CP; exclude writable forwarding to verifier. |
| L097 | P2Prime proof slice identity | No. Needs same-world digest binding/collision/log proof. |
| L098 | P2Prime complete ASF8 public identity | P1 origin alone is insufficient. The existing digest/collision route can establish identity without ASC8 origin; reconstruction cuts and source association still required. ASC8 provenance helps a separate authenticated-state route. |
| L180 | deployment alias of protected CP key/version L094–L096 in literal ledger | No new ASC8 binder exists in S2X_RuntimeRetention.lean. The adopted scope additionally assigns ASC8 provenance here as a separate deployment obligation; P1 is necessary for that added obligation, not for the literal CP history fields. |

Sources: design/PREMISE-LEDGER-20261025.md rows149–153,250 and expanded aliases;
docs/research/100bit-spend-path-20261013/lean/S2X_RuntimeRetention.lean
(CheckpointVersionBinding/checkpoint_sites), R9PoolRuntimeBinding.lean
(Inputs/P2Prime); design/POOL-LIFECYCLE-SCOPE-20261026.md exact property section.

Thus no literal numbered row is an ASC8-only premise. L180 is the owner-assigned
umbrella for the extra ASC8 origin/retention property. Proving P1 does not prove
upstream master/lane correctness or finish any of L094–L098 by itself. This is a
priority distinction for the lead, not a proposal to change or lower scope.
