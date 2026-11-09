# PCT_ HANDOFF: phase P5 (a lane) of the (bk) extraction-provenance campaign

Target not yet established. This job changes no ledger row, trust row, RSL, security contract or shipped source.

Branch `codex/pc-prov-p5-20261109` from research dc66d6e331e. Host workspace `/home/dombarker/project-offloads/codex-pc-prov-p5-20261109/`.

## Claims (exact)
For the 41 modules of PCT_PARTITION a_identical (19) and a_pending (22), reached definitions: 309. Per definition status in `PCT_STATUS.json`:
PROVED_RFL 82, PROVED_UNFOLD 100, FAILED 35 (with goal and class), TEXT_IDENTICAL_ONLY 15 (not a Lean fact), NOT_COVERED 77 (no verified text-identical receipted fresh emission pass; routed to P2).
A proved entry means: the theorem `PRVEq.<M><tag>.<name> : @PRVFresh_.. = @<gate>.<name>` compiled in the verify bundles PCT_L015/L016/L017 (all exit 0; 262 `#print axioms` lines, only propext/Classical.choice/Quot.sound; no sorry, native_decide; maxHeartbeats only the Aeneas header 1000000). Types structures are proved by generated Equiv; inductives and non-simple structures are text-identical only. Fresh Funs are compiled against the gate Types/externals by name; externals are inherited gate assumptions, listed in `PCT_HAND_MODELS.json` (122 entries; 13 resolved to extracted-from-frozen-source declarations, 109 define in imported gate modules not examined; none resolved as hand-written in the text examined: this is NOT a finding that none exist).
Reclassified to c1 (`PCT_FOR_P2P3.json` reclassified_modules): AspisR1WithdrawalValidation.Types, S8Kani2MutableSource, VTop_Model, Port3_NativeBatchBody, Port3_NativeGeometryBody, Port5Q2_ReaderWeights, Port5Q2_ReaderValidate, Op4P_Extract.Types, NDH_Reference.Funs. Queue items: 127 (FAILED to P3, others to P2).
Generator rerun: NMP_prepare.Funs retained copy (candidate 0cf7ed44) is byte equal to the output of NMP_parameterize.py on the receipted raw emission (`PCT_GENERATOR_RERUN.json`). No generator was found for NNG_verify_finish, NMT_*; no claim there.
Compiled source: self-copy controls (53 candidates, probe stage) for the modules with unproved/uncovered definitions are in `PCT_STATUS.json` compiled_source. Modules fully proved against a receipted emission have no control (see PCT-C2).

## What ran
Lean scopes L001-L021 (serial; 6G/8G, swap 0, 180 s): L001-L003 and L004-L007, L012-L014 probes; L008-L011 and L015-L017 verify rounds (earlier selection superseded by prepare2); L018-L021 controls. L019 timed out (180 s, exit 124) and was not rerun unchanged. No extraction scopes. Peak RSS max 5.23 GB (L018). Per-scope receipts and axioms in PCT_L0nn/receipt.json and PCT_ATTEMPTS.jsonl. L001-L011 belong to the superseded first selection (prepared.json, gen/old, gen/round1, round2); the deliverables derive from L012-L017.
Local only: partition rerun (6 min) for the fresh-symbol map.

## Remaining
35 FAILED (mostly fresh declarations that do not elaborate against the gate environment; two heartbeat timeouts), 77 NOT_COVERED, 15 text-only, 9 reclassified modules, NND citations for AdapterRwModel not done, hand-model resolution for 109 names, NNG/NMT generator byte equality, controls for FIn_WeightsFuns.
