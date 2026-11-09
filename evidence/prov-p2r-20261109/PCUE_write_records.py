#!/usr/bin/env python3
import json,hashlib,collections,subprocess
from pathlib import Path
H=Path(__file__).resolve().parent;EV=H.parent
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
# ---------------- TOOLS
tools=[
 ('PCUE_gen_equalities.py','../prov-p2d-20261109/PCUD_gen_equalities.py (sha256 %s; the P2d copy with PCUD patches 1-4)'%sha(EV/'prov-p2d-20261109/PCUD_gen_equalities.py'),[
  'prefix PCUD_ -> PCUE_',
  'change 1 (from PCWA change 1, PCWA_TOOLS.json): fresh declarations are emitted in a namespace NESTED INSIDE the gate namespace; statements use the qualified fresh name; the former `open <gate namespace>` of the fresh namespace is removed',
  'change 2 (P2a PARSE-1): parse_blocks peels leading namespace/section/open/set_option/variable/universe lines of a raw block so a declaration directly after such a line is recognised',
  'change 3: --kind {funs,types} override (single-file gate modules; as in PCUA_gen_equalities.py)',
  'change 4 (P2d NO_COMMON_LEAN_NAME, aspis_core.* prefix): --name-map JSON {fresh name: gate name}; the planner builds it deterministically (rule: gate name = fresh name with a leading `aspis_core.` added or removed). Statements and delta use the gate name; identity of types is checked modulo the map (textual rename in the comparison only, emitted fresh text is never rewritten). For Funs passes, fresh carrier type names missing in the gate are resolved by `open <gate ns>.aspis_core` (prefix added in the gate) or `abbrev <fresh type> := <gate type>` (prefix added in the fresh emission); both are recorded in the report (alias_types, name_map)',
  'change 5 (P2a STRUCT-1): structure-field names that are Lean keywords are emitted as «name» in generated Equiv literals; tested in PCUE_L026 on a synthetic structure with a field named `at` (the real verifier.Reader is only in overflow-off emissions, so it is not retested on it)',
  'change 6: every generated equality is preceded by `set_option maxHeartbeats 200000 in` (LOWERED from the default, never raised) after the PCUE_L009 timeout',
  '--open-extra NS (from PCUA_gen_equalities.py): extra namespace opened inside the fresh namespace (used for RPz7_FIp_NativeDots: FIo_Native)',
  'the driver PCUE_gen.py always passes --prune-fresh (PCUD patch 3)']),
 ('PCUE_partition.py','../prov-p2d-20261109/PCUD_partition.py',['prefix only (imported for uncomment())']),
 ('PCUE_run.py','../prov-p2d-20261109/PCUD_run.py',['prefix PCUD_ -> PCUE_; host base codex-pc-prov-p2d-20261109 -> codex-pc-prov-p2r-20261109']),
 ('PCUE_run_host.py','../prov-p2d-20261109/PCUD_run_host.py',['prefix only']),
 ('PCUE_bundle.py','../prov-p2d-20261109/PCUD_bundle.py',['prefix only']),
 ('PCUE_index.py / PCUE_plan.py / PCUE_match.py / PCUE_gen.py / PCUE_final.py / PCUE_hand_models.py / PCUE_write_records.py / run_scope.sh / chain1-3.sh',None,['new PCUE scripts: overflow-checks-on emission index, plan, driver, aggregation']),
]
rows=[]
for f,orig,ch in tools:
    r=dict(file=f,origin=orig,changes=ch)
    if '/' not in f and (H/f).exists(): r['sha256']=sha(H/f)
    rows.append(r)
for f in ['PCUE_index.py','PCUE_plan.py','PCUE_match.py','PCUE_gen.py','PCUE_final.py','PCUE_hand_models.py','run_scope.sh']: rows.append(dict(file=f,sha256=sha(H/f)))
(H/'PCUE_TOOLS.json').write_text(json.dumps(dict(schema='PCUE_TOOLS/1',starting_generator_copy='evidence/prov-p2d-20261109/PCUD_gen_equalities.py',starting_generator_sha256=sha(EV/'prov-p2d-20261109/PCUD_gen_equalities.py'),
  pcwa_changes_source='evidence/prov-p4a-20261109/PCWA_TOOLS.json (read with git show research:; PCWA_gen_equalities.py change 1 adopted; change 2 --fresh-prelude NOT adopted)',tools=rows),indent=1))
# ---------------- CLASSIFICATIONS
cl=[
 ('C1','Scope of the redo','Only overflow-checks-on fresh emissions count (ruling 2026-11-09). All emissions P2a/P2d used (NMH_*, NHR_*, NKM_circle, NNG, NMT, PCQ_E4xx, FILE: retained sources) are not in the overflow-on set (receipt check in PCUE_final.old_info: fresh_overflow_on false). Every definition they proved or failed is therefore re-planned against PCUE_EMISSION_INDEX.json (PCQC_E001-E012, E022, E023; PCQ_E037-E040); a definition with no same-named (or prefix-variant) declaration there is NO_FRESH_EMISSION, with the earlier status and its emission kept in superseded_earlier_status. An earlier proof is not carried over.'),
 ('C2','Name-level coverage','Coverage is by Lean declaration name (and the aspis_core. prefix variant), not by Rust symbol; the Lean compile against the gate constants is the check. Declarations with kind axiom/opaque in the overflow-on emission do not count as coverage.'),
 ('C3','Passes with no common declaration','Five planned passes (CurrentCompactCallerTypesV1_p2, NJA_Multiproof_Types, R1CandidateWideParserSource, RPz7_FIo_NativeTypes_p3, Stage2ContinuationTypes_p2) have zero common declarations after pruning and were not compiled; their definitions are TEXT_ONLY_NOT_COMPARED / NO_FRESH_EMISSION in the status file.'),
 ('C4','Status TEXT_ONLY_NOT_COMPARED','The overflow-on emission declares the name but the generator produces no equality for the declaration shape (inductives, structures with parameters or non-simple fields, external types). Text identity is not a proof and is never counted as one.'),
 ('C5','Status GATE_SOURCE_UNAVAILABLE','Five modules (NFN_ExtractedGeometry, CurrentClaimSumModel, ClaimsUnrolledParentTypes, S8Kani2MutableSource, CurrentWideEqSemanticV7; 60 definitions) have a gate source with several namespaces (or none readable at the recorded path), which the generator rejects by design. Not a claim about the overflow-on emissions; name-level presence is recorded informationally per definition. Needs a generator extension for multi-namespace gates, not done here.'),
 ('C6','Heartbeat budget','After PCUE_L009 timed out (F4 bundle, 180 s, default per-theorem budget), each generated equality was given `set_option maxHeartbeats 200000 in` (lowered, never raised). The four fast_dots equalities of RPz7_FIp_NativeDots then failed with (deterministic) timeout at isDefEq/whnf in PCUE_L018 and are recorded as FAILED (heavy defeq on the fast_dots loops), not as semantic differences. The old shape (one bundle with NativeFuns x4, NativeDots, DotDecode, S1NativeCompact, R1CandidateFieldParsers) is retired; replacement: one bundle per heavy module (F4a/F4b/F4c/F4d/F6).'),
 ('C7','Round-3 ingest discarded','Ingesting a verification log (round 3) re-emitted failed equalities as live theorems (the generator keeps failed status only for the probe round). The round-3 states and re-emitted files were deleted; the round-2 files were regenerated from the probe logs and are byte-identical (after the first line) to the bundles compiled in PCUE_L020-L025 (checked by diff). The final state is state2 of each label.'),
 ('C8','CONFIG_MISMATCH rule','A FAILED equality whose normalized token diff contains a wrapping_/checked_/overflowing_/saturating_ operation on either side, or that is blocked by such a callee, is CONFIG_MISMATCH, with fresh_body and gate_body recorded. This applies only now that the fresh side is overflow-checks-on. The 8 cases: fast_pairing.canonical.reduce (gate wrapping_shr/add/sub vs fresh checked >>> + -), Dot.finish and EbyKDot.finish (blocked by reduce), EbyKDot.push (gate Usize.wrapping_add), transport.Variant.row_loop.body (gate Usize.wrapping_mul), row_loop and row (blocked), NMT_stage1_owned stage1_owned (gate Usize.wrapping_add). The gate model is an overflow-off (wrapping) model of source that an overflow-checks-on build compiles to checked arithmetic.'),
 ('C9','LIB-1 (wrapping_shr/shl shift type) with overflow-on emissions','Not reproduced as an elaboration failure: PCQC_E011 and PCQC_E008 contain no wrapping_shr/wrapping_shl (the frozen source uses plain shifts and arithmetic, emitted checked), so the fresh declarations elaborate against the gate library. The previously blocked equalities (NativeDots, transport row/row_loop) now surface either as CONFIG_MISMATCH (gate uses wrapping_*) or, for the fast_dots loops, as a heartbeat timeout (C6). Not otherwise touched.'),
 ('C10','Type names of gate vs fresh (aspis_core. prefix)','Planner rule only: the gate name is the fresh name with a leading `aspis_core.` added or removed (nothing else). Fresh carrier types in Funs passes are resolved by `open <gate ns>.aspis_core` or `abbrev`, never by editing a proof. Types that the gate lacks entirely (e.g. aspis_core.field.wide_exact.WideExact in AspisR1WeightsFieldCurrent) stay unresolved and the equality is FAILED (fresh declaration did not elaborate).'),
 ('C11','PROVED_EQUIV vs PROVED_RFL for structures','Generated isomorphisms of structures (Equiv) are PROVED_EQUIV (as in P2a); P2d called these PROVED_RFL. They are isomorphisms, not type equalities.'),
 ('C12','Conditional proofs','2 PROVED definitions reach an external name of the fresh emission that resolves by name to a gate constant (PCUE_HAND_MODELS.json, proved_definitions_conditional_on_it); they are conditional on that gate constant being the intended model.'),
 ('C13','Probe receipts','PCUE_L001 (probe, the first pass before --prune-fresh), L006-L019 probes contain error recovery output; only L020-L025 (verification of the final files) and L026 (synthetic STRUCT-1 test) are deliverable evidence for proofs. L002-L005 were clean probes whose files were later verified inside L020/L021.'),
]
(H/'PCUE_CLASSIFICATIONS.json').write_text(json.dumps(dict(schema='PCUE_CLASSIFICATIONS/1',target_established=False,classifications=[dict(id=a,topic=b,text=c) for a,b,c in cl]),indent=1))
# ---------------- scope table
tbl=[]
for n in range(1,27):
    a='PCUE_L%03d'%n;r=json.load(open(H/a/'receipt.json'))
    tbl.append(dict(attempt=a,target=r['module'],exit=r['exit_status'],wall_seconds=round(r['wall_seconds'],1),peak_rss_kib=int(r['peak_rss_kib']),swaps=r['swaps']))
(H/'PCUE_SCOPES.json').write_text(json.dumps(dict(schema='PCUE_SCOPES/1',source_revision=json.load(open(H/'PCUE_L001/receipt.json'))['source_revision'],note='26 of 40 Lean scopes, 0 extraction scopes, one at a time; caps 6G/8G swap 0 tasks 64 timeout 180 s unraised',scopes=tbl),indent=1))
for t in tbl: print(t['attempt'],t['target'],t['exit'],t['wall_seconds'],round(t['peak_rss_kib']/1048576,2))
