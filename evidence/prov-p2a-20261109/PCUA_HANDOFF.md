# PCUA_ HANDOFF: phase P2a (generated equality modules, hub cluster)

Target not yet established. No ledger row, trust row, RSL, security contract or shipped source changed. Branch `codex/pc-prov-p2a-20261109`, base research `53b46ab6c86`. Frozen source `4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`. Host workspace `/home/dombarker/project-offloads/codex-pc-prov-p2a-20261109/`. 11 of 40 Lean scopes, 0 extraction scopes.

## 1. Claims established (all statements are `PRVFresh_<M>.f = <gate>.f` against the gate's compiled constants, or a generated `Equiv`)

Per hub-cluster gate module (counts of reached definitions; full list `PCUA_EQ_STATUS.json`):

| gate module | PROVED_RFL | PROVED_UNFOLD | PROVED_EQUIV | FAILED | TEXT_ONLY | not paired | NO_FRESH | reused P0 |
|---|---|---|---|---|---|---|---|---|
| RPz7_FIp_DotDecode | 0 | 4 | 0 | 0 | 0 | 0 | 0 | |
| RPz7_FIp_NativeDots | 0 | 0 | 0 | 5 | 0 | 1 | 0 | |
| RPz7_FIo_NativeFuns | 7 | 9 | 0 | 3 | 0 | 2 | 5 | |
| RPz7_FIo_NativeTypes | 2 | 0 | 4 | 0 | 5 | 0 | 2 | |
| Stage2ContinuationTypes | 2 | 0 | 2 | 1 | 9 | 0 | 6 | |
| AspisR1CurrentWide.Types | 1 | 0 | 3 | 0 | 0 | 0 | 0 | |
| AspisR1CurrentWide.Funs | 0 | 1 | 0 | 10 | 0 | 0 | 10 | |
| S1M31EmbeddingSourceV1 | 1 | 0 | 2 | 0 | 0 | 0 | 1 | |
| AdapterRwTypes | | | | | | | | 15 (P0 PCO_L006, not redone) |
| CurrentWideMulCanonical, CurrentWideEqSemanticV7, AspisR1CanonicalQRawUnified.{Types,Funs}, FIo_QRaw{Types,Funs} | | | | | | | 3+4+4+8+4+8 | |
| RPz7_FIo_NativeExternal | no annotated definition reached (c0), nothing to compare | | | | | | | |

Final replay scopes (exit 0, only propext / Classical.choice / Quot.sound on every one of the 60 `#print axioms` lines, no sorry, no axiom, no native_decide, no raised heartbeats): `PCUA_L006` (bundle G1: DotDecode, NativeDots obligations, NativeTypes x Q415, Stage2 x Q415, NativeFuns x Q415, CurrentWide Types and Funs, S1M31; 37 theorems), `PCUA_L009` (bundle H1v: NativeFuns x E410, NativeTypes x E416, Stage2 x E003; 12), `PCUA_L010` (bundle H2v: NativeTypes x E003, Stage2 x E010; 11). Fresh emissions are named per job in `PCUA_JOB_STATUS.json` (`fresh_dir`).

Strength of each status: PROVED_RFL / PROVED_UNFOLD is equality of the fresh Aeneas constant and the gate constant (unfold = delta both sides, rewrite with the already proved callee equalities, rfl). PROVED_EQUIV is a generated isomorphism of structures, not a type equality. TEXT_IDENTICAL_ONLY (14 inductives and complex structures) is not a proof. 6 PROVED definitions are conditional on a fresh External-template name that resolves by name to a gate constant (`conditional_on_external_boundaries` in the status file): `EbyKDot.push` reaches the opaque `Dot.push` (the P1b Aeneas failure), `EbyKDot.finish` / `Q.from_wide` / `trace.value` reach the opaque `WideExact` (from_limbs / to_limbs), DotDecode `CM31/QM31.from_le_bytes` reach the `core::option` Try functions. These are recorded, not discharged (PCUA_HAND_MODELS.json, 55 entries, record only).

## 2. Findings that matter for P3 (`PCUA_FOR_P3.json`, 91 obligations plus classified differences)

- SEM-1 checked vs wrapping arithmetic is systematic: every CurrentWide `M31.add/sub` and everything above them (`CM31.add/sub/mul`, `mul_by_r`, `M31.double`), the `fast_dots` index arithmetic and the transport `row_loop` shifts. Exact witnesses and domains are in the file. Two cases (`M31.mul`, `reduce_u64`) never overflow: they need a bound lemma, not a domain restriction. Same class as P0's `M31.neg`.
- LIB-1: fresh emissions do not elaborate against the gate's Aeneas library for `wrapping_shr`/`wrapping_shl` (shift-amount type). This blocks `NativeDots` and the transport `row`/`row_loop` before any semantic comparison; it is a toolchain-pairing question for the lead, not decided here.
- NAME-1/NAME-2: NativeDots calls DotDecode's decoders under a different module name; the aspis-core items `mul_by_r`/`reduce_u64` are named without the `aspis_core.` prefix in NFG_InverseRef. The DotDecode equalities (4 proved) are the callee side of NAME-1.
- Compiled-source control for `AspisR1CurrentWide.Funs` (PCUA_L011): 25 of 25 declarations proved with the committed candidate as the fresh emission, so the two candidates (identical declaration text) are consistent with the compiled constants.

## 3. What did not happen

No fresh emission exists (and no extraction was run) for: CurrentWideMulCanonical, CurrentWideEqSemanticV7 (no standalone `eq` for the aspis-core field types in any emission), the QRaw modules (cut crate), `Dot.push`/`push_loop` (Aeneas error, PCQ_B_FAILURES S016), `Weights.raw` closures (S022), the aspis-core items `WideExact.add/sub/mul`, `r0::heap::filled`, `r0::transport::order`, `source_from_m31`, the `QueryGeometry.for_range` closures. P1a (aspis-core, aspis-statement) is still running; when it merges, re-run NativeFuns/CurrentWide/NativeDots with its emissions via `python3 PCUA_jobs.py` (add a job row; same two commands, probe then verify).

## 4. Reproduce

All tools are renamed copies of the PCO_ tools (`PCUA_TOOLS.json`: original sha256, every change). `PCUA_jobs.py gen|gen2|bundle` drives the generator; `PCUA_run.py PCUA_L### lean PRVEq_bundle_X` runs one scope (admission, share and disk checks as in PCO_run.py); then `PCUA_status.py`, `PCUA_hand_models.py`, `PCUA_eqstatus.py`, `PCUA_for_p3.py`. Gate sources are exact `git show research:<path>` copies in `gate_src/` (paths in `PCUA_HAND_MODELS.json` / `PCUA_CLASSIFICATIONS.json`). Scope table (target, exit, wall s, peak RSS MiB, swaps 0 everywhere): L001 A1 probe 1/12.0/5235; L002 B1 NativeDots probe 1/77.3/5534; L003 C1 types probe 0/5.1/3838; L004 F1 CurrentWide+S1M31 probe 1/3.9/2598; L005 D1 NativeFuns probe 1/5.7/3779; L006 G1 final 0/18.5/5414; L007 H1 probe 1/4.7/3790; L008 H2 probe 0/4.5/3803; L009 H1v final 0/4.4/3800; L010 H2v final 0/4.3/3804; L011 control 0/41.9/2586. No memory kill, timeout or cap change; source revision of each scope is 53b46ab6c86 with the new evidence directory untracked at launch (dirty flag in the receipts). Probe receipts contain sorryAx (error recovery) and are not deliverables.

## 5. Remaining

Next deliverables: (1) lead decision on LIB-1 (emitter/library pairing) because it blocks the loop-bearing functions; (2) P1a emissions, then NativeFuns `mul_by_r`/`reduce_u64`, CurrentWide wide-exact items; (3) P3 proofs for SEM-1 with domains, TYPES-1 inductive isomorphisms, STRUCT-1 `verifier.Reader`; (4) P4 for the cut-crate modules.
