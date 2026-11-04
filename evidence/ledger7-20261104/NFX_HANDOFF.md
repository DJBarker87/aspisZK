# Ledger refresh 7 handoff

**167/587 CLOSED, 89 QUALIFIED, 331 OPEN. Target not yet established.**
Branch `codex/cx-ledger7-20261104`; no push. NFX_LEDGER.md is the readable
ledger; NFX_LEDGER.json is delivered as `.json.xz` plus its uncompressed
`.sha256` under the 20 MB rule. NFX_ROUTES.json covers every occurrence;
NFX_TRUST_USED.json gives current accepted scopes and direct uses.

| Scope | Total | CLOSED | under (ae) | QUALIFIED | OPEN |
|---|---:|---:|---:|---:|---:|
| TX1 | 345 | 88 | 2 | 42 | 215 |
| TX2 | 242 | 79 | 2 | 47 | 116 |
| S | 97 | 8 | 0 | 89 | 0 |
| Q | 149 | 142 | 4 | 0 | 7 |
| D | 343 | 21 | 0 | 0 | 322 |

Four Q/S occurrences overlap and count once globally. TX2:046 and TX2:211
remain OPEN inventory defects outside D ∪ Q ∪ S. There are 434 functions,
90 fully CLOSED. Routes among CLOSED rows: 153 plain (y), four (ad), four
(ae), six source reclassifications; P6/D188 option-A transport is retained
for every applicable bridge, never removed.

Q has **2/2 roots CLOSED**. S's source validators still report **7/7 CLOSED**,
but its headline-coherent roots are **0/7: all seven are QUALIFIED**. D's
common entry function remains OPEN in both transactions (0/2 transaction
root occurrences). NFQ's 21 helper occurrences are admitted; no NFT_/NFU_
evidence had landed in research at final preparation (NFX_RESEARCH_CHECK.json).
Pool is outside the verifier inventory and remains OPEN.

The discrepancy from the expected S headline is the main finding. Faithful
NFJ-only import passes; adding RPx fails duplicate original/canonical Prepared
ownership. The old S forest has exactly 650 missing references in 15 modules.
85 active packet occurrences import it; four more depend on qualified callee
claims. NFX_S_PACKET_PATHS.json and NFX_COHERENCE_DENIALS.json give exact paths.
No passing source validator is promoted across that defect.

The final reduced combined forest imports the admitted Q, D helpers and
independent S helpers together with `AspisR1.RPx_Deployed.deployed`.
NFX_AUDIT.json: **263 raw roots, standard axioms only, no collectAxioms
mismatch, all eight fixtures passing in the same binary**. The full
13,126-module scan has zero dangling references, incompatible owners or import
mismatches. Compatible cached theorem replicas (1,569) are disclosed. The
old packet/Phase/Prepared owners and old reachability entry are absent;
canonical object variants and two unchanged common libraries are explicitly
pinned in NFX_LEGACY_FAMILY_PINS.json. See NFX_FINDINGS.md, not a name-only ban.

Unchanged predecessor validation was actually rerun: NEN, NEZ, NET, NFE,
NFK, NFS (both additive chains), NFJ and NFQ. Historical aggregate inputs use
private byte-pinned Git views; no validator gate was waived. Fresh isolated NEI
output is also compared explicitly. NFX_TESTS rejects 18 mutations. The last
five host slots print full theorem statements/domains and headline premises;
no new theorem or assumption was added. `#print axioms` is retained for every
printed top theorem, with only propext/Classical.choice/Quot.sound or none.

**40/40 host slots charged**, 36 normal receipts, four charged own input/client
failures; 27 normal successes and nine failures. Zero Kani/extraction/Rust or
ELF rebuild. Peak RSS 6,903,780 KiB; swaps 0. Every submitted proof/audit uses
6G high / 8G max / swap0 / Tasks64; Lean -M7000, optimized audit linkers,
one own capped scope at a time. No timeout, memory kill or cap raise. Exact
commands, source/dependency/Aeneas pins, revisions, exits, time/RSS/swap and
axiom outputs are retained in NFX_ATTEMPTS.jsonl and per-attempt receipts.

Retained cache: `/home/dombarker/project-offloads/codex-cx-ledger7-cache-20261104`.
Final objects: `NFX_exports_20261104`; audit binaries: `NFX_native_20261104`.
NFX_EXPORT.json and the import/priority/S-view manifests pin their bytes.
No cache or key was deleted. An interrupted child changed absolute paths in
one predecessor report; the captured diff was restored exactly and all later
writes were isolated. Final hygiene checks require no changes outside NFX.

Remaining: canonical retarget/replay of the 89 qualified S rows; D's roots
and incoming Prepared/powers/prepare domains; Pool production-prefix/helper/
carrier/account association and joint reachable settlement; L159/L181 native
realization obligations, L187 cold coherent replay, L188 final trust/axiom/
artifact audit, and both inventory defects. RuntimeReturnData (nonempty
1..1024, ASR8=792), RuntimeMemcmp, RuntimePersistence, SDK/std and P6/D188
remain explicit. L154 is a statement parameter; digest/error are op43/op44.
The 100-bit per-attempt target, privacy and two transactions are unchanged.

Stage commits: `142fb7b40d9` policy; `c116695d4db` predecessor/candidate stage;
`0fe46a191d2` combined audit and qualifications. Final artifact/handoff stage
is the commit containing this version. No final manifest/cold release claim.

Inherited ELF pins (not rebuilt or rehashed by NFX):

- Default `f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4`.
- Devnet `63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299`.
- Pool `121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548`.

NFX_HOST_END.json verifies all 12 retained exports and no active owned build;
only 20 compiled scratch files under the private workspace were removed.
The owned cache, authored sources and evidence remain. Restore the exported
objects into the recorded workspace or put `NFX_exports_20261104` before
`NFX_priority`, SInt2 root/objects and the fallback cache in LEAN_PATH; exported
bytes match the measured objects. No further host slot is available.

Reproduce evidence checks locally: `python3 evidence/ledger7-20261104/NFX_tests.py`
and `python3 evidence/ledger7-20261104/NFX_artifacts.py --check-output`.
These launch no prover. NFX_LEDGER_FINAL2 also updates generic `coverage` to
the current counts; the prior value remains in NFX_prior_coverage. The report
fix adds no closure and required no unchanged formal replay.
