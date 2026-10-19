# Actual query-scan success and decoder range

The retained generated `QueryScan.scan` success now yields the exact Q22 model transition and the successful decoded word list used by that transition. A second theorem proves every returned decoded word is below 262144 (18 bits), using the actual generated map callback and its exact masking operation. The successful-scan endpoint discharges the decoder-success condition; the range is not an independent assumption about attacker input.

The packet also retains the eight-block stopping/fallback model and its single-block handoff, a generic actual map-state output lemma, and the bridge through the exact generated Array.map aliases. These reuse the previously checked finite recurrence/correspondence packet at `3a18592d1`.

This does not establish the byte-level block_rank/little-endian formula or the original source outer eight-block wrapper correspondence. The unrolled query-scanner source candidate remains unadopted; it is not substituted for the original callback loop. No verifier hash-call count, Merkle acceptance or checkpoint hashing claim is included.

| Checked source | Exit | Wall seconds | Peak process RSS KiB | Cgroup peak bytes | Swap bytes |
| --- | --- | --- | --- | --- | --- |
| QueryScanEightBlockHandoff-v19.lean | 0 | 12.247 | 1,830,760 | 1,075,814,400 | 0 |
| QueryScanActualScanBridge-v3.lean | 0 | 1.505 | 2,512,532 | 280,969,216 | 0 |
| QueryScanMapStateLemma-v1.lean | 0 | 1.504 | 2,522,544 | 292,974,592 | 0 |
| QueryScanMapStateLemma-v4.lean | 0 | 1.305 | 2,516,672 | 282,820,608 | 0 |
| QueryWordsArrayMapAll-v6.lean | 0 | 1.605 | 2,508,640 | 274,612,224 | 0 |
| QueryWordsRange-v6.lean | 0 | 1.404 | 2,521,980 | 283,811,840 | 0 |
| QueryScanMaskCallExact-v4.lean | 0 | 6.02 | 2,237,608 | 1,075,793,920 | 0 |

All printed theorem axiom reports contain only `propext`, `Classical.choice`, `Quot.sound`. Each focused NUC receipt retains exact target/source/object/compiler/import hashes, revision, commands, cgroup limits and ordered roots; no scope used swap. All 65 payload hashes, eight source/object owner pairs and seven new successful receipts were checked on publication. The finite correspondence owner is reused from the prior packet, rather than presented as a new compile.

Archive SHA256: `33298fd43c18de84e16c6a22a9664c22d1b35e861c0c9d7e011deaa54d12de98`.
Owner manifest SHA256: `0aa1ee4b955add59e4e044ef5f0ae74176bfeae46e9547d2e962edf9a8ac1cc6`.
Readable sources are under `lean-candidates/current-query-scanner-20261019`. No full manifest replay was run.
