# S10 H5 re-pin — 23 October 2026

## Stage 1: adopted source and artifact reproduction

Compiler input is `4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`;
comparison baseline is re-pin2's `d50042542971c7a11bab8c3662896ccf834daa59`.
The retained snapshot has 7,978 inputs. Five change: H5's Core two-write helper,
canonical constructor, weights arithmetic and owned adapter tail scanner,
plus cfg-gated `RealR1_client` module wiring (`r1p-check`, excluded here).
`source-delta.json` retains exact patches; unchanged pre-stage adapter helpers
are independently pinned in `child-pins.json`.

H5 changes actual child source. The requested strict confinement to adapter
caller glue cannot hold against re-pin2. Child identity must be assessed per
body rather than asserted from historical certificates.

Builds use private host caches, optimized SBF compilation, `-j 4`, platform
tools v1.52 and the retained feature/program-ID configuration. Each build
has MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64, with a checked
host reservation. Time is spent in compilation and diagnostic emission.
`build-manifest.json` records hashes, sizes, full commands and raw receipts.
The reused harness hard-codes an old revision; its raw field is explicitly
corrected by the rehashed source manifest, never silently relabelled.
For devnet no expected H5 hash was supplied: expected=null/byte_identical=false
means discovery, not an ELF mismatch failure (actual build exits 0).

No shipped source or session-A candidate is edited. Historical S10 packets
are untouched. No Lean compilation or unrelated regression is run.
No binaries/objects/keys enter commits; generated keys remain on the host.
`#print axioms`: N/A for compiler/Python evidence. S10 stays incomplete;
S2 caller identities and final source/model correspondence remain open.

| Mode | SHA-256 | Wall s | Peak RSS KiB | Swap |
|---|---|---:|---:|---:|
| default | `f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4` | 31.913 | 686076 | 0 |
| devnet | `63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299` | 31.48 | 683772 | 0 |
| pool | `121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548` | 32.529 | 678960 | 0 |

`snapshot-exclusions.json` names the ten tracked files outside the retained
snapshot, including the cfg-excluded host client/tests and xtask non-build
files. This snapshot is a selected SBF build input set, not a complete source
repository census.

## Stage 2: regenerated machine/compiler and ordering evidence

The same retained algorithms regenerate linked/deployed ELF call tables,
raw aliases, relocations, independent LLVM disassembly, frontier observations,
MIR CFGs, typed instances and constant-callback analysis. Physical calls are
1,637/1,637/2,202 (default/devnet/Pool); callx stays 36/36/80. Raw alias call
records are 1,644/1,644/2,220 and are checked separately. No final DWARF inline
map is available. Fifteen constant SHA targets and six null observers retain
their explicit scope; 131 library sites stay open. All 189 callback negative
controls reject.

Every one of the **140** selected-call dominance facts survives against
re-pin2, with **zero re-selections, zero changed block coordinates and zero
changed selected-body hashes**. `ordering-repin-map.json` retains exact
old/new selected call keys and independently checked current graph cuts.
The owned stage caller is outside these selected child/wrapper observations.
No source_order/model_order or new Lean graph specialization is inferred.

Two collector setup failures are retained: collect-host-v2 read Pool before
its capture finished, and elf-symbol-kinds-host retained old directory labels.
The completed Pool build and a corrected path adapter allow replacement runs;
no SBF rebuild or cap increase was needed. The failed script is retained under
`tools/s10-repin3-20261023/historical/` where its bytes differ.
