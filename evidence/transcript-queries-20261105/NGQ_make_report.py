from pathlib import Path
import json,hashlib,lzma,collections
E=Path(__file__).resolve().parent
load=lambda n:json.loads((E/n).read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
receipts=[load(str(p.relative_to(E))) for p in sorted(E.glob('NGQ_L[0-9][0-9][0-9]/receipt.json'))]
raw=[load(str(p.relative_to(E))) for p in (sorted((E/'NGQ_audit').glob('batch*/proof*.json'))+sorted((E/'NGQ_audit/finalnew').glob('proof*.json')))]
fixture=load('NGQ_audit/fixtures/fixtures.json')
scan=[json.loads(l) for l in (E/'NGQ_LOADED_scan.jsonl').read_text().splitlines()]
imports=json.loads(lzma.decompress((E/'NGQ_CACHE_IMPORTS.json.xz').read_bytes()))
exports=load('NGQ_FINAL_HOST.json');binary=next(r for r in exports['exported'] if Path(r['destination']).name=='NGQ_ProofDriver')
native=load('NGQ_NATIVE_RESULTS.json')
audit={
 'status':'PASS for conditional model roots, ax2 controls and coherent scan; TX1:168 OPEN',
 'frozen_revision':'4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',
 'headline':'AspisR1.RPx_Deployed.deployed',
 'security_target_established_by_this_job':False,
 'new_composed_rows':0,
 'budget':{'limits':{'kani':60,'lean_support':60,'extraction':1},'charged':{'kani':60,'lean_support':len(receipts)+1,'extraction':1},'lean_support_receipts':len(receipts),'lean_support_prelaunch':'NGQ_L013 (fingerprint inspection, no compiler launched; conservatively charged)','unsubmitted_not_charged':[],'native_verdicts':dict(collections.Counter(r['status'] for r in native['runs']))},
 'raw_groups':raw,
 'raw_root_count':sum(len(r['results']) for r in raw),
 'fixtures':fixture,
 'walker_pin':load('NGQ_WALKER_PIN.json'),
 'binary':dict(binary,mode_reuse='Single optimized link NGQ_L047; same unchanged binary for NGQ_L048..L054 and NGQ_L060. Only the four new roots were audited at L060, followed by a new scan because its import closure changed. No per-mode relink or unchanged full replay.'),
 'scan':{'receipt':'NGQ_L060/receipt.json','artifact':'NGQ_LOADED_scan.jsonl','sha256':sha(E/'NGQ_LOADED_scan.jsonl'),'expected_imports':'NGQ_EXPECTED_IMPORTS.jsonl','expected_imports_sha256':sha(E/'NGQ_EXPECTED_IMPORTS.jsonl'),'expected_origin':'Committed NGK/NGP baselines plus source-derived NGQ headers, never candidate scan','modules':len(scan),'declarations':sum(r['declarations'] for r in scan),'references':sum(r['edges'] for r in scan),'dangling':sum(len(r['dangling']) for r in scan),'incompatible_owners':sum(len(r['duplicate_owners']) for r in scan),'import_mismatches':sum(not r['imports_match'] for r in scan),'compatible_cached_replicas':sum(len(r.get('cached_replicas',[])) for r in scan)},
 'excluded_lean_attempts':[r['attempt'] for r in receipts if r['exit_status']!=0],
 'extraction':{'receipt':'NGQ_E001/receipt.json','status':'TOOL FAILURE, no emitted Lean output','llbc':'NGQ_E001.llbc.xz','raw_sha256':(E/'NGQ_E001.llbc.sha256').read_text().strip()},
 'source_checks':'NGQ_SOURCE_VALIDATION.json',
 'packet_checks':'NGQ_PACKET_VALIDATION.json',
 'seed':{'files':len(imports),'bytes':sum(r['bytes'] for r in imports),'manifest':'NGQ_CACHE_IMPORTS.json.xz','raw_sha256':(E/'NGQ_CACHE_IMPORTS.json.sha256').read_text().strip()},
 'retained_cache_export':{'files':len(exports['exported']),'bytes':exports['export_bytes'],'manifest':'NGQ_FINAL_HOST.json','never_deleted_cache':True,'final_append_manifest':'NGQ_FINAL_EVENTS_HOST.json','final_append_new_bytes':load('NGQ_FINAL_EVENTS_HOST.json')['new_copy_bytes'],'final_object_path_precedes_old':'NGQ_final_events_20261105'},
 'trust_change':{'added':[],'removed':[],'discharged':[]},
 'claims':'Same-input ordered position/full-Result/log equality conditional on chronological native Trace; all physical producer gaps disclosed in NGQ_REMAINING.md. No model-only/native-fragment promotion; no cold release replay or ELF rebuild.'}
audit['seed']['raw_sha256']=(E/'NGQ_CACHE_IMPORTS.json.sha256').read_text().strip()
(E/'NGQ_AUDIT.json').write_text(json.dumps(audit,indent=1)+'\n')
print(json.dumps({'lean_support_charged':len(receipts)+1,'raw_roots':audit['raw_root_count'],'seed_files':len(imports),'seed_bytes':audit['seed']['bytes'],'rows_closed':0}))
