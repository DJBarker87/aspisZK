from pathlib import Path
import hashlib,json,lzma,re,csv
E=Path(__file__).resolve().parent
rs=list(map(json.loads,(E/'NIV_ATTEMPTS.jsonl').read_text().splitlines()));assert len({r['attempt'] for r in rs})==len(rs)
ks=[r for r in rs if r['attempt'].startswith('NIV_K')];ls=[r for r in rs if r['attempt'].startswith('NIV_L')]
status=[]
for r in ks:
 out=lzma.decompress((E/r['attempt']/'stdout.log.xz').read_bytes()).decode()
 success='VERIFICATION:- SUCCESSFUL' in out
 control='VERIFICATION:- FAILED' in out and bool(re.search(r'\*\* 1 of \d+ failed',out)) and 'unwinding assertion' not in out.lower() and r['module'].endswith('_wrong')
 status.append(dict(attempt=r['attempt'],module=r['module'],classification='bounded_positive' if success else 'matched_failing_control' if control else 'diagnostic',exit=r['exit_status']))
for r in ks:
 a=r['attempt']
 for suffix,key in [('-graph-check.json','graph_matches_frozen'),('-lock-check.json','unchanged'),('-erasure-check.json','passed'),('-isolation.json','allowed')]:
  assert json.loads((E/(a+suffix)).read_text())[key],a+suffix
roots=json.loads((E/'NIV_AUDIT_ROOTS.json').read_text())['groups'][0]
for n in [27,28,29,30,31,32,33,34,35,36]:assert next(r for r in ls if r['attempt']=='NIV_L%03d'%n)['exit_status']==0
out=lzma.decompress((E/'NIV_L033/stdout.log.xz').read_bytes()).decode();assert all("'"+root+"'" in out for root in roots)
scan=[json.loads(l) for l in lzma.decompress((E/'NIV_NIV_LOADED_scan.jsonl.xz').read_bytes()).decode().splitlines()]
assert all(x['imports_match'] and not x['dangling'] for x in scan)
assert len(ks)==120
x=dict(schema_version=1,status='GATES_PASS_NO_COMPOSED_ROW_CLAIM',target_established=False,headline='AspisR1.RPx_Deployed.deployed',frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',kani_budget=dict(limit=120,used=len(ks),classifications={k:sum(r['classification']==k for r in status) for k in set(r['classification'] for r in status)}),formal_budget=dict(limit=90,scopes_used=len(ls),lean_compiles=sum(r['kind']=='lean' for r in ls)),extraction_budget=dict(limit=1,used=1,receipt='NIV_L022',warm_builds=1),raw_ax2=dict(receipt='NIV_L033',roots=len(roots),allowed=['propext','Classical.choice','Quot.sound']),fixtures=dict(receipt='NIV_L032',count=8),NFX=dict(receipt='NIV_L034',loaded_modules=len(scan),dangling=0,imports_mismatched=0),combined_import='NIV_L027',native_credit='NONE: native domains and SDK/full-result producer cuts remain incomplete',new_trust_rows=[],composition_trust='Owner option A retained/reclassified, never removed',quarantined_NIV_harnesses=[],suspended_writable_static_NIV_harnesses=[],shipped_files_changed=False,ELFs_rebuilt=False,ELF_statement='No shipped-file change; inherited release pins are not new rebuild evidence',scope_caps=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64),no_unchanged_timeout_rerun=True,kani=status)
(E/'NIV_AUDIT.json').write_text(json.dumps(x,indent=1)+'\n')
(E/'NIV_CLOSED.json').write_text(json.dumps(dict(schema_version=1,status='NO_NEW_COMPOSED_ROWS',functions=[],rows=[],new_composed_functions=0,new_composed_rows=0,gate='NIV_AUDIT.json',credit_waits_for_next_ledger=True),indent=1)+'\n')
base=E.parent/'ledger12-20261107/NIR_LEDGER.json.xz'
(E/'NIV_LEDGER_DELTA.json').write_text(json.dumps(dict(schema_version=1,baseline=str(base.relative_to(E.parent.parent)),baseline_archive_sha256=hashlib.sha256(base.read_bytes()).hexdigest(),baseline_raw_sha256=hashlib.sha256(lzma.decompress(base.read_bytes())).hexdigest(),frozen_revision=x['frozen_revision'],changes=[],new_composed_rows=0,reason='No complete native producer packet; all pre-existing row statuses preserved; NIS candidates await their ledger gate'),indent=1)+'\n')
with (E/'NIV_RESULTS.tsv').open('w') as f:
 w=csv.writer(f,delimiter='\t');w.writerow(['attempt','kind','target','exit','wall_seconds','peak_rss_kib','swaps','source_revision','axioms'])
 for r in rs:w.writerow([r['attempt'],r['kind'],r['module'],r['exit_status'],r['wall_seconds'],r['peak_rss_kib'],r['swaps'],r['source_revision'],json.dumps(r['print_axioms'])])
(E/'NIV_TARGET_DIRS.json').write_text(json.dumps({r['attempt']:dict(recorded=r.get('env',{}).get('CARGO_TARGET_DIR'),designated='/home/dombarker/project-offloads/codex-cx-slice-d-entry7-20261107/NIV_target',cargo_relevant_scope=r['kind'] not in ['lean','link','audit','inspect'],note='Historical Lean-only omissions retained honestly; no Cargo ran in those scopes')for r in rs},indent=1)+'\n')
print(json.dumps({k:x[k] for k in ['status','kani_budget','formal_budget','raw_ax2','NFX']}))
