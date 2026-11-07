from pathlib import Path
import json,hashlib,lzma,re,subprocess
E=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rows=[json.loads(l) for l in (E/'NMD_ATTEMPTS.jsonl').read_text().splitlines()]
excluded=set(json.loads((E/'NMD_BUDGET.json').read_text())['no_kani_launch'])
actual=[r for r in rows if r['kind']=='kani' and r['attempt'] not in excluded];assert len(actual)==120
limits={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
for r in rows:
 full=json.loads((E/r['full_receipt']).read_text());assert full['limits']==limits,r['attempt'];assert int(full['swaps'])==0,r['attempt']
 assert sha(E/r['full_receipt'])==r['full_receipt_sha256'],r['attempt']
roots=json.loads((E/'NMD_AUDIT_ROOTS.json').read_text())['roots'];raw=[]
for i in range(2):raw+=json.loads((E/'NMD_audit'/('batch'+str(i))/('proof'+str(i)+'.json')).read_text())['results']
assert set(r['root'] for r in raw)==set(roots)
assert all(set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'} for r in raw)
assert all(r['equal'] for r in raw)
verdicts=[]
for r in rows:
 if r['kind']!='kani':continue
 a=r['attempt'];log=lzma.decompress((E/a/'stdout.log.xz').read_bytes()).decode()
 v='NO_KANI_LAUNCH' if a in excluded else 'TIMEOUT' if 'timed out' in log.lower() else 'PASS' if 'VERIFICATION:- SUCCESSFUL' in log else 'FAIL' if 'VERIFICATION:- FAILED' in log else 'COMPILE_ERROR' if 'could not compile' in log else 'NO_HARNESS_MATCH' if 'Failed to match' in log else 'TOOL_SETUP_ERROR'
 verdicts.append(dict(attempt=a,target=r['module'],verdict=v,credit=False,informational=a in ['NMD_K083','NMD_K084','NMD_K085','NMD_K086','NMD_K087','NMD_K088']))
(E/'NMD_RUN_VERDICTS.json').write_text(json.dumps(verdicts,indent=1)+'\n')
ret=json.loads((E/'NMD_RETENTION.json').read_text());export=json.loads((E/'NMD_EXPORT.json').read_text())
scan=json.loads((E/'NMD_audit/scan/scan.json').read_text());assert scan['exit_status']==0
baseline=E.parent/'ledger23-20261110/NLO_LEDGER.json.xz'
audit=dict(target_established=False,branch='codex/cx-cut-pilot-20261107',headline='AspisR1.RPx_Deployed.deployed',ledger_baseline=dict(path=str(baseline),sha256=sha(baseline),CLOSED=580,QUALIFIED=0,OPEN=19),ledger_changes=[],candidate_roots=[],budget=dict(kani_actual_invocations=len(actual),kani_scoped_attempts=sum(r['kind']=='kani' for r in rows),no_kani_launch=sorted(excluded),lean_compiles=sum(r['kind']=='lean' for r in rows),lean_limit=60,kani_limit=120,extraction=0,total_capped_scopes=len(rows)),full_combined_audits=2,combined_imports=['NMD_L006','NMD_L013'],final_scan=dict(attempt='NMD_L014',exit_status=0,modules=ret['loaded_modules'],zero_dangling_duplicate_owners_import_mismatches=True),raw_ax2=dict(attempts=['NMD_L015','NMD_L016'],roots=raw,standard_only=True,collector_agrees=True),fixtures=dict(attempt='NMD_L009',controls=8,exit_status=0,reused_unchanged_audit_binary=True),resources=dict(limits=limits,all_verified=True,peak_rss_kib=max(int(r['peak_rss_kib']) for r in rows),swaps=0,scoped_wall_seconds=sum(r['wall_seconds'] for r in rows),retention=ret),retired_timeouts=[dict(attempt=r['attempt'],target=r['module'],wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib']) for r in rows if r['attempt'] in ['NMD_K057','NMD_K070','NMD_K071','NMD_K123']],native_actual_064_producer=False,method_status='Controlled minimal carrier/record patterns only; no complete actual064 binding pattern',remaining='NMD_REMAINING.md',hypotheses=dict(discharged=['Minimal shape/compiler controls and source-fold equality only','Candidate child RowSpec from corrected NLT_CompleteRoot.root'],retained=['Actual same-parent native segment/physical decoder','Complete actual065 heap/allocator/borrow/ownership/effect footprint','Public1880 and Root0 caller clauses for241','All existing P6/D188 option-A compiler/std/allocator/ABI/runtime/source-to-ELF and cryptographic trust'],added=[],reviewed_transcription_admitted=False),frozen=dict(selected_crates_and_r1_program='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',lock_sha256='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef',graph_and_postlock_verified_actual_runs=len(actual),kmx_patch_sha256='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67',pool_owner_pin='b936275465',pool_not_reached=True,unused_pool_corpus_finding='NMD_UNUSED_POOL_FINDING.json',shipped_source_changes=False,elf_rebuilds=0,elf_hashes_inherited_only={'default':'f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4','devnet':'63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299','Pool':'e0e49c344d35575116c0359450315ea4334bfb03006551727f67c04a8cfe09dc'}),tool_findings=dict(k3_comparison='NMD_K3_COMPARISON.json',quarantined_false_pass=['NMD_K088'],nonpinned_no_credit=['NMD_K084','NMD_K085','NMD_K086','NMD_K087'],pin_or_quarantine_changed=False,generic_wrapper_rejection=['NMD_K118','NMD_K119'],ordinary_stub_contract_metadata_rejection='NMD_K126',guard_constructor_scope='free RefCell<u8> only',program_constructor_scope='one mutable u8; exactly Ok or Custom(any u32)'),export=export,security_metric_changed=False,privacy_or_two_transaction_design_changed=False,pushes=0)
(E/'NMD_AUDIT.json').write_text(json.dumps(audit,indent=1)+'\n')
(E/'NMD_CLOSED.json').write_text(json.dumps(dict(target_established=False,closed=[],candidates=[],support_only=['NMD_CutState','NMD_SegmentFold','NMD_CandidateFold','NMD_ComputedFold'],new_top_theorems=8,validation='Individual compiles and final coherent import/NFX/raw ax2 pass; no actual native064 producer'),indent=1)+'\n')
(E/'NMD_LEDGER_DELTA.json').write_text(json.dumps(dict(baseline='evidence/ledger23-20261110/NLO_LEDGER.json.xz',baseline_sha256=sha(baseline),baseline_counts=dict(CLOSED=580,QUALIFIED=0,OPEN=19),changes=[],result_counts=dict(CLOSED=580,QUALIFIED=0,OPEN=19),credit_waits_for_next_ledger_gate=True),indent=1)+'\n')
(E/'NMD_HANDOFF.md').write_text(f'''# NMD cut-point pilot handoff

**Target not yet established. No complete actual064 binding pattern, native parent producer, candidate row root or ledger promotion.** Branch codex/cx-cut-pilot-20261107; stage commits local, no push. Ledger23 remains580 CLOSED /0 QUALIFIED /19 OPEN.

## Established support and method findings

NMD_METHOD.md/NMD_SHAPES.json give exact templates, domains, controls and verdicts. Local-enum Result contracts pass shape controls after exhaustive Arbitrary. Actual frozen mark(None,Parsed) has controlled local empty-modifies/unit-return evidence and stability (K078–K082). Ref/RefMut verified stubs reject; safe typed constructors pass only for a free RefCell<u8> with value/token corruption controls. ProgramResult verified stubs reject; the one-cell finite-domain constructor route passes after separating native contract-check and annotation-free caller builds, with body identity pinned. K126 exposed the contract-closure compiler error. No SDK/allocator packet is inferred from these minimal shapes.

The arbitrary-content generic local-record channel passes at original lengths1880/57607/1768 with an argument-swap failure and KMX negative. A concrete verified wrapper cannot replace a generic callee: K118/K119 reject H versus concrete Hash despite matched generic arity. This leaves the full actual065 footprint uninstalled. Parser full-allocation contracts K057/K070/K071 timed out90s; the four-cell ProgramResult K123 shape also timed out. All four are retired, no cap/timeout increase or unchanged rerun.

Informational K-3: identical-source, same-workspace0.67 falsely passes the original NEF case; private0.68 correctly fails it and passes the literal-None control. No pin/quarantine change or static-writing credit. See NMD_K3_COMPARISON.json.

## Lean and gate

Four new modules/eight top theorems compile. NMD_ComputedFold.run/transcription/same_fold/fold give the complete-outcome G fold, literal equality to NLW's SAME selected-child transcription, and use the corrected NLT_CompleteRoot candidate including independent C04 stops. NMD_SegmentFold.fold remains RowSpec-parameterized; actual ChildAt/Segments/physical interpretation are explicit missing native premises. Root0/public1880 stay241 caller clauses. No actual decoder is assumed proved.

Exactly two combined audits. Final L013 imports the ledger23 canonical NLS module (receipt filename NLO_COMBINED_IMPORT.lean), NLW/NLT and NMD with AspisR1.RPx_Deployed.deployed. Final NFX exits0 on{ret['loaded_modules']} modules with zero defects;9 raw roots agree with collectAxioms and use only propext/Classical.choice/Quot.sound. Eight unchanged-binary fixtures pass. Per-target command, exit, wall, RSS, swap, source/dependency/Aeneas hashes and complete axioms are in NMD_ATTEMPTS.jsonl and scoped receipts.

## Resources, scope and next work

120/120 actual Kani invocations;129 native scopes including9 prelaunch failures;7/60 Lean compiles;0 extraction. Unused Lean allowance is explained call by call in NMD_REMAINING.md: remaining064 obligations need actual native producer/full footprint, or241 caller material outside this slice. All remaining mathematical folds were completed. Every scope has6G high/8G max/swap0/tasks64; Lean-M7000. PeakRSS{audit['resources']['peak_rss_kib']}KiB, swaps0; no memory kill. Admission/disk refusals were waited out. Own host writes{ret['workspace_bytes']}bytes, free{ret['free_bytes']}bytes; caches/TMP/targets retained. No shared/sibling/session-A write or key/fund action.

NLW export was verified and copied FIRST, then NLT and ledger23; imported hashes are retained. Final own export:{export['path']} ({export['bytes']}bytes). NMD_CLOSURE_PINS pins{ret['closure_objects']} final objects;239 Aeneas objects remain unchanged. Prefix this export to NMD_ENV.json's existing dependency path when importing.

Selected verifier/R1 bodies and every invoked dependency graph/lock are frozen, offline and deployed-feature checked. The inherited corpus also contains15 historical UNUSED Pool files differing from ownerb936; no selected dependency closure reaches asp is-pool (spelled aspis-pool in manifests). NMD_UNUSED_POOL_FINDING.json records this; no Pool-source parity or ELF verification is claimed. No shipped file changed or ELF rebuilt. Defaultf8c0ec72…,devnet63ad3e9c…,owner Pool e0e49c34… are inherited only. No new trust row or change to100-bit per-attempt soundness/privacy/two transactions.

Next: a different validated actual-parser window/frame mechanism and the actual065 full-footprint bridge. Minimal record/constructor patterns cannot be promoted to those obligations without that evidence. NMD_CLOSED/NMD_LEDGER_DELTA are empty; credit waits for a future ledger gate.
'''.replace('asp is-pool (spelled aspis-pool in manifests)','aspis-pool'))
print(json.dumps({'actual_kani':len(actual),'lean_compiles':audit['budget']['lean_compiles'],'raw_roots':len(raw),'peak_rss_kib':audit['resources']['peak_rss_kib'],'target_established':False,'ledger_changes':0}))
