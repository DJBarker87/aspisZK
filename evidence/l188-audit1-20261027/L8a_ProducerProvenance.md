# D188 PublicPreparation producer provenance

**Finding D188-P: this cohort's producer is not the byte-for-byte extraction of the frozen release source. No faithful-extraction-of-the-release-pin claim is established.** This is a provenance finding, not evidence of an accepted-path attack or a theorem contradiction. Equivalent transformed source would need an explicit accepted association; compilation alone does not establish it.

## Exact selected cohort

The historical larger producer is identified by revision `e5c186ba3bcbbf9a0cc5878077aa8848853a65cc` and historical Types/Funs objects e1d3e2db…/06348080…. Those are object hashes, not source hashes. The fresh cohort does not import those historical objects. In the recorded LEAN_PATH order, `L8a_HostPins.json` resolves:

| Module | Fresh selected source SHA-256 | Fresh selected object SHA-256 |
|---|---|---|
| AspisR1PublicPreparation.Types | `b45ee7357278642101b81933252e81f5068c937487acfdebb4f82f991c91bb83` | `45660c0b10ce70596c0d83453a6d70243055bfe568a7791813b30170d7db2989` |
| AspisR1PublicPreparation.Funs | `544b75b962ade326ff1069b6986805a175cc90db1c592b1c524dffcd94693d2d` | `933f376d3f58f29770fa585d0df01f1ef4f1b377a205e8a9219b72f8a4b3f07f` |

Types comes from the e5c bridge's union/named-discriminant source. Funs comes from the Prepared-only naming-adapted source. This is precisely the previously replayed coherent selection, not substitution of a producer during this audit. RPz5_057/058 receipts and RPz8_selected-source-check.json bind the actual selected sources. The e5c bridge's alternate Funs source is `c3dd345a41c971c00dcae53a4799eaeebccfd953abda3ad7390da78a5a07995b`, not the selected 544b… source. The smaller Types is `0514a63e697cddb5b3a96aca33121b19f9feeecd669a6489a9c368459d27bf27`; it is not selected.

## Raw extraction and release comparison

The retained Tx1 archive is `442a5a86c5f07dffdcc6d10d42d0c401bae312d306105a8254dd6eed059684bf`, 12,444,031 bytes. Its recorded successful Aeneas output is:

- raw Types `bb4ccfd7a77b6e45de16181113c888febda2ecf8c23bdad55c1919fe92762c3e`;
- raw Funs `f4aee2661033aeaf820623a7decb3687e2617ae50a2ad4b41e78b253025a1de1`;
- LLBC `cca010037fefc042d1df364a05edbbf1547ad4cc8bd476bfc14f450f79433b89`;
- source-pins JSON `613973e3763e8a48a2ba13599a9326af31a6e1f026af8fb3252a9b6105aa4bb0`;
- Aeneas executable `4632746db1bf6c3953f2971078965a2a5a8ad6cf5f75636b46b397bc50c550b5`.

Its root is `crate::verifier::tx1`, with explicit opaque child boundaries, at e5c186ba3. The archive's 30 raw source cuts all match the git e5c files and their recorded offsets/hashes. The union retains Prepared declarations and adds five Tx1 carriers. It is explicitly an adapter/union, not raw generation. Neither fresh selected source equals either raw Types/Funs output, or any file found in the 454-file `lean-candidates/*/extraction/**/*` scan. The requested manifest.json/SHA256SUMS/check-extraction.py triplet is the v10 four-dots packet, not PublicPreparation; it names neither selected producer hash.

S10 re-pin3 identifies release compiler input `4bb3b3f51e16b4525f1d10336e2b0bcbbd775387` for the adopted H5 ELFs. Compared with that pin, **22/30 historical source cuts still occur verbatim; eight do not**: `verify_observed`, `verifier_error`, `dot_type`, `prepared_new`, `prepared_claim`, `query_geometry`, `tx1`, `tx1_finish`. `L8a_ReleaseCutComparison.json` records all paths, raw fragment hashes, historical file/cut checks and release file hashes. `L8a_e5c-release-source.diff` records the exact git source changes. These are source-byte observations, not a semantic inequivalence theorem. They preclude silently relabelling the historical kit as a complete literal extraction of the release pin.

D188 (LOG 2026-10-23 16:40) defines a source-extraction trust boundary, not an unconditional certificate that any producer represents any release revision. `S2W_DigestExtraction.AeneasExtraction` names stage1_owned, stage2_owned and digestSource; neither it nor the binding contract embeds a producer revision. `digest-source-reuse.json` certifies only the unchanged three-line digest syntax, excludes failed Charon004, and leaves source interpretation explicit. The e5c Tx1 cut and the frozen release/compiler pin therefore remain distinct pins. Safe Vec/Box model trust does not bridge different source bodies, and unsafe raw writes remain outside it.

## Executed check and stopped reproduction chain

`L8a_Check001` runs the **unmodified** retained `check-extraction.py` (SHA-256 `1c3e4d21a10f4dda8c70d4a3a904c3914fa05d843388a9e4dce50b955903b636`) on the build host in one admitted 6G/8G/Swap0/Tasks64 scope. Its layout uses symlinks to existing generated/LLBC/runs data and a few small pinned text/JSON inputs; no second corpus or Rust target is created. It passes the v10 output hashes and executable-body byte comparison against the v6 source. Full command, source pins, exit/wall/RSS/swaps and stdout are retained. **That passing result covers four-dots, not PublicPreparation.**

The original PublicPreparation recorded Aeneas command and receipt are retained as `L8a_command.json` and `L8a_receipt.json`. Its exact executable path and LLBC path are both absent on the host (`L8a_HostPins.json`). No extraction command was launched with substitute tools, no toolchain was reconstructed, and no different source pin was substituted. Reproduction of the specific PublicPreparation producer is therefore **blocked before launch**, not a failed or passing extraction run. The raw archive retains LLBC bytes, but restoring it alone cannot replace the absent pinned executable.

## Ruling-ready outcome

D188 producer provenance cannot be marked closed for the frozen H5 release. The audit establishes a coherent, explicitly selected historical/adapted producer cohort and exact hash mismatches to raw historical extraction; it does not establish faithful extraction of frozen pin 4bb3b3f51… . A lead-owned next step must supply the exact pinned extractor and a source/adapter association to the release pin, or adopt a newly certified release extraction and replay its dependent closure. Such adoption is outside this audit. No original/session A source, ledger, contract, shipped code, ELF or key changed.
