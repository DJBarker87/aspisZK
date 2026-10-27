# S10 replay and final L186 manifest

The existing tools/s10-repin3-20261023 algorithms were rerun with literal
private-workspace/output path relocation only. Low2_check_manifest.py verifies
that all four copied tool sources are exactly those path substitutions:
collect-host, ordering-host, cfg-host and ordering-map. No new S10 algorithm,
call selection, compiler correctness theorem or weaker ordering fact was added.
The ELF collector checked every pinned deployed ELF and equality of deployed/
linked .text; ordering/CFG tools regenerated all140 MIR graph-cut certificates;
ordering-map checked every selected call against the prior frozen map.
All140 preserved, zero changed MIR bodies, zero coordinate changes.
These remain compiler evidence under P7, not source/model execution identities.

Initial metadata analyses failed: source dependency path contained ../ aliases;
ELF collector expected the failed default-v1 directory; ordering collector lacked
its private packet directory; CFG analysis consequently lacked its input.
All failed capped receipts are retained. V2 normalizes source paths, points
only the default build coordinate to successful default-v2 and supplies the
private output directory. No build rerun, timeout, memory kill or cap increase.
One local analysis-driver NameError was corrected before any scope launched.

Final check:
python3 -B evidence/lowering2-20261026/Low2_check_manifest.py

Low2_final_receipt.json: exit0, wall0.235210625s, peak36716544bytes, swaps0.
The final source-to-ELF manifest binds all479 unique certificate file/hash pins
on478 files:2,794 exact references,14 recorded bridged references.157 Rust
files are actual compiler inputs,11 are Cargo configurations and310 are
inventory files outside these release compilation features (including tests,
examples and other programs).240 verification-kit/reference pins are checked
against retained exact bytes and explicitly kept outside release membership.
No inventoried or verification-only source is falsely called compiled.
All1,243 private snapshot files match the pinned local source after building.

Existing S4 all_input_source_equivalence source and exact old/new bodies are
pinned. Its reused #print axioms line contains only propext, Classical.choice,
Quot.sound. No new Lean theorem was added and no Lean/Kani invocation ran.
The final dependency/source/tool/manifest hashes are in the receipts.

L186's evidence gates are satisfied under the owner's S10/P7 ruling. Retire
this implementation-lowering premise while retaining P7 and all other named
extraction/P6/library/runtime trust. No other ledger row or headline100-bit
claim is closed. The authoritative ledger itself is outside this worker's
write scope; this packet is its concrete removal evidence.

## Capped analysis receipts

| Target | Exit | Wall s | Peak RSS KiB | Swaps |
|---|---:|---:|---:|---:|
| collect_builds-v2 | 0 | 0.281 | 42652 | 0 |
| collect_host-v2 | 0 | 0.21 | 38664 | 0 |
| ordering_host-v2 | 0 | 0.211 | 67600 | 0 |
| cfg_host-v2 | 0 | 0.133 | 45560 | 0 |

All use source revision8953c28138c7e3bc31a9109e84ab3a9864090057,
MemoryHigh6G, MemoryMax8G, MemorySwapMax0 and TasksMax64. Original capped
receipts retain the launcher's historical revision field; actual source is
explicit in each Low2 invocation receipt. Axioms N/A for Python/SBF checks.
