from pathlib import Path
import json,lzma,hashlib,re,subprocess
E=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rs=[json.loads(x) for x in (E/'NLM_ATTEMPTS.jsonl').read_text().splitlines()]
lean=[r for r in rs if r['kind']=='lean'];native=[r for r in rs if r['kind']=='kani' and r['attempt'] not in ['NLM_K001','NLM_K002']]
assert len(lean)==140 and len(native)==40
for r in rs:
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},r['attempt']
 assert str(r['swaps'])=='0',r['attempt']
for r in native:
 a=r['attempt'];g=json.loads((E/(a+'-graph-check.json')).read_text());lock=json.loads((E/(a+'-lock-check.json')).read_text())
 assert g['graph_matches_frozen'] and not g['new_package_tuples'] and not g['edge_errors'],a
 assert lock['unchanged'] and lock['before']==lock['after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef',a
 assert r['env']['CARGO_NET_OFFLINE']=='true' and 'opt-level=3' in r['env']['RUSTFLAGS'],a
for positive,negative,_ in json.loads((E/'NLM_NATIVE_PAIRS.json').read_text())['pairs']:
 positive='NLM_'+positive;negative='NLM_'+negative
 rp=next(r for r in rs if r['attempt']==positive);rn=next(r for r in rs if r['attempt']==negative)
 p=lzma.decompress((E/positive/'stdout.log.xz').read_bytes()).decode();n=lzma.decompress((E/negative/'stdout.log.xz').read_bytes()).decode()
 assert rp['exit_status']==0 and 'VERIFICATION:- SUCCESSFUL' in p,positive
 assert rn['exit_status']!=0 and 'VERIFICATION:- FAILED' in n and re.search(r'\*\* 1 of \d+ failed',n),negative
 assert 'unwinding failures' not in n and 'undetermined' not in n,negative
modules=json.loads((E/'NLM_MODULES.json').read_text())+['NLM_COMBINED_IMPORT']
selected=json.loads((E/'NLM_SOURCE_SELECTORS.json').read_text())
for m in modules:
 h=sha(E/(m+'.lean'));good=[r for r in lean if r['module']==m and r['exit_status']==0 and h in r['source_hashes'].values()]
 assert good,('no current passing source',m)
 selected[m]=good[-1]['attempt']
roots=json.loads((E/'NLM_AUDIT_ROOTS.json').read_text())['roots'];walks=[]
for p in (E/'NLM_audit').rglob('proof*.json'):
 r=json.loads(p.read_text());assert r['exit_status']==0;walks+=r['results']
assert sorted(r['root'] for r in walks)==sorted(roots)
assert all(r['equal'] and r['collect_axioms']==r['walked_axioms'] and set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'} for r in walks)
scan=[json.loads(x) for x in lzma.decompress((E/'NLM_LOADED_scan.jsonl.xz').read_bytes()).decode().splitlines()]
assert all(not r['dangling'] and not r['duplicate_owners'] and r['imports_match'] for r in scan)
f=json.loads((E/'NLM_audit/fixtures/fixtures.json').read_text());assert f['exit_status']==0 and len(f['results'])==8 and all(r['equal'] for r in f['results'])
export=json.loads((E/'NLM_EXPORT.json').read_text())
assert export['source_hashes']=={m:sha(E/(m+'.lean')) for m in modules}
retained=json.loads((E/'NLM_RETENTION.json').read_text());assert retained['own_bytes']<30_000_000_000
pins=json.loads(lzma.decompress((E/'NLM_CLOSURE_PINS.json.xz').read_bytes()));ap=[x for x in pins.values() if x['module'].startswith(('Aeneas.','AeneasMeta.')) or x['module'] in ['Aeneas','AeneasMeta']]
assert ap
report=dict(status='SOURCE_MODEL_SUPPORT_AUDIT_PASS_INCOMPLETE_NATIVE_FOLDS',target='AspisR1.RPx_Deployed.deployed',target_established=False,complete_parameterized_native_folds=0,closed_rows=[],proposed_promotions=[],source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_selectors=selected,budget=dict(kani=40,lean=140,extraction=0,remaining_kani=0,remaining_lean=0,capped_native_receipts=42,pre_kani_failures=['NLM_K001','NLM_K002']),combined_source_sets=1,full_combined_audits=1,scan=dict(receipt='NLM_L146/receipt.json',exit_status=0,modules=len(scan),dangling=0,incompatible_owners=0,import_mismatches=0,cached_replicas=sum(len(r['cached_replicas']) for r in scan)),raw_ax2=dict(roots=len(walks),standard_only=True,collector_walk_agreement=True),fixtures=dict(count=8,passed=True),frozen_graph=dict(actual_runs=40,offline=True,lock_unchanged=True,resolved_packages=441,historical_lock_orphans=['aspis-r1-cert-build','aspis-r1-cert-check','aspis-z4b-probe']),source_limits='MemoryHigh6G MemoryMax8G MemorySwapMax0 TasksMax64; Lean-M7000; native90s/scope180s unchanged',max_peak_rss_kib=max(int(r['peak_rss_kib']) for r in rs),swaps=0,source_revisions=sorted(set(r['source_revision'] for r in rs)),aeneas_objects_pinned=len(ap),closure_pins='NLM_CLOSURE_PINS.json.xz',export=export['path'],export_objects=len(export['files']),native_domain_findings='NLM_NATIVE_DOMAIN_FINDINGS.json',hypotheses='NLM_HYPOTHESIS_INVENTORY.json',unadmitted='NLM_UNADMITTED.json',remaining='NLM_REMAINING.md',trust='Contract semantic transport reclassified under existing P6/D188; not removed; no new runtime trust; pending CPI-readonly item unused.',shipped_source_changes=False,elf_rebuild=False,elf_status='Inherited golden values only; not remeasured; Pool uses owner-amended e0e49c344d35575116c0359450315ea4334bfb03006551727f67c04a8cfe09dc')
(E/'NLM_AUDIT.json').write_text(json.dumps(report,indent=2)+'\n')
(E/'NLM_SOURCE_SELECTORS.json').write_text(json.dumps(selected,indent=1)+'\n')
print(json.dumps(dict(modules=len(modules),roots=len(walks),scan_modules=len(scan),lean=140,kani=40,export=export['path'],closed=0)))
