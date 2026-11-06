"""Offline report validation. No proof/Kani process is launched by this script."""
from pathlib import Path
from collections import Counter
import json,re,hashlib,lzma,subprocess
E=Path(__file__).resolve().parent;H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
records=[json.loads(f.read_text())for f in sorted(E.glob('NKQ_[LK][0-9][0-9][0-9]/receipt.json'))];by={r['attempt']:r for r in records};assert len(by)==len(records)
assert all(r['env']['CARGO_TARGET_DIR']=='/home/dombarker/project-offloads/codex-cx-tx1-driver-20261108/NKQ_target'for r in records)
assert all(int(r['swaps'])==0 for r in records)
assert all(int(r['peak_rss_kib']or 0)<8*1024*1024 for r in records)
for r in records:
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 a=r['attempt'];ad=json.loads((E/(a+'-admission.json')).read_text());assert ad['exit']==0 and ad['reservation']['allowed']is True
 disk=json.loads(sorted(E.glob(a+'-disk-*.json'))[-1].read_text());assert disk['free']>=40_000_000_000
 assert r.get('source_revision') and r.get('command')
ks=[r for r in records if r['attempt'].startswith('NKQ_K')];ls=[r for r in records if r['attempt'].startswith('NKQ_L')];assert len(ks)==70 and len(ls)<=120
native=[]
for r in ks:
 assert r['env']['CARGO_NET_OFFLINE']=='true' and r['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
 a=r['attempt'];graph=json.loads((E/(a+'-graph-check.json')).read_text());lock=json.loads((E/(a+'-lock-check.json')).read_text());assert graph['graph_matches_frozen'] and lock['unchanged'] and lock['before']==lock['after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
 raw=(E/a/'stdout.log').read_text();verdict='PASS'if 'VERIFICATION:- SUCCESSFUL'in raw else'FAIL'if 'VERIFICATION:- FAILED'in raw else'COMPILE_ERROR'
 if verdict=='PASS':assert r['exit_status']==0
 elif verdict=='FAIL':assert r['exit_status']!=0 and re.search(r'\*\* 1 of \d+ failed',raw) and ('assert_failed_inner'in raw or 'Failed Checks: assertion failed:'in raw)
 else:assert a in ['NKQ_K001','NKQ_K002','NKQ_K005','NKQ_K030']
 native.append(dict(attempt=a,verdict=verdict,exit=r['exit_status']))
assert Counter(x['verdict']for x in native)==dict(PASS=33,FAIL=33,COMPILE_ERROR=4)
(E/'NKQ_NATIVE_CLASSIFICATIONS.json').write_text(json.dumps(native,indent=1)+'\n')
fixtures=json.loads((E/'NKQ_audit/fixtures/fixtures.json').read_text());assert fixtures['exit_status']==0 and len(fixtures['results'])==8
for i,r in enumerate(fixtures['results']):
 assert r['equal'] and (len(r['walked_axioms'])==1 if i<4 else not r['walked_axioms'])
loaded=[json.loads(l)for l in(E/'NKQ_LOADED_scan.jsonl').read_text().splitlines()];assert all(not x['dangling']and not x['duplicate_owners']and x['imports_match']for x in loaded);assert by['NKQ_L077']['exit_status']==0
manifest=json.loads((E/'NKQ_AUDIT_ROOTS.json').read_text());expected=Counter(x for g in manifest['groups']for x in g);seen=Counter();mismatches=[];groups=[];standard={'propext','Classical.choice','Quot.sound'}
for i,g in enumerate(manifest['groups']):
 p=E/'NKQ_audit'/('proof'+str(i))/('proof'+str(i)+'.json');j=json.loads(p.read_text());assert Counter(x['root']for x in j['results'])==Counter(g)
 assert len(j['print_axioms'])==len(g)
 bad=[]
 for r in j['results']:
  assert not(set(r['walked_axioms'])-standard) and not(set(r['collect_axioms'])-standard)
  seen[r['root']]+=1
  if not r['equal']:mismatches.append(dict(group=i,**r));bad.append(r)
 assert j['exit_status']==(1 if bad else 0)
 groups.append(dict(group=i,exit=j['exit_status'],roots=len(g),wall_seconds=j['wall_seconds'],peak_rss_kib=j['peak_rss_kib'],swaps=j['swaps']))
assert seen==expected
assert len(mismatches)==1 and mismatches[0]['root']=='NHC_DecodeModel.decoder_error'and mismatches[0]['collect_axioms']==[] and set(mismatches[0]['walked_axioms'])==standard
compression_count=0
for f in(E/'NKQ_audit').rglob('*.xz'):
 raw=lzma.decompress(f.read_bytes());assert hashlib.sha256(raw).hexdigest()==f.with_suffix('.sha256').read_text().strip();compression_count+=1
comparison=json.loads((E/'NKQ_PREDECESSOR_COMPARISON.json').read_text());assert comparison['status']=='PASS'and not comparison['mismatches']
pins=json.loads(lzma.decompress((E/'NKQ_CLOSURE_PINS.json.xz').read_bytes()));assert pins['scan_pass']and pins['modules']==len(loaded)
assert hashlib.sha256(lzma.decompress((E/'NKQ_CLOSURE_PINS.json.xz').read_bytes())).hexdigest()==(E/'NKQ_CLOSURE_PINS.json.sha256').read_text().strip()
mods=json.loads((E/'NKQ_MODULES.json').read_text());success={}
for r in ls:
 if r.get('module')in mods['modules']and r['exit_status']==0:success[r['module']]=r
assert len(success)==len(mods['modules'])
for m,r in success.items():
 current=E/'NKQ_generated'/f'{m}.lean';snapshot=E/r['attempt']/'sources'/'NKQ_generated'/f'{m}.lean'
 # S2W source snapshots are represented by the receipt source hashes; normalize accepted layout below.
 assert snapshot.exists() and H(current)==H(snapshot)==r['source_hashes'][f'NKQ_generated/{m}.lean']
 text=current.read_text();assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',text)
 assert all('sorryAx'not in x for x in r['print_axioms'])
assert by['NKQ_L071']['exit_status']==0 and len(by['NKQ_L071']['print_axioms'])==55
assert all('sorryAx'not in x for x in by['NKQ_L071']['print_axioms'])
assert not subprocess.check_output(['git','diff','--name-only','HEAD','--','crates','programs'],text=True).strip()
assert not [f for f in E.rglob('*')if f.is_file()and f.stat().st_size>20_000_000]
status=dict(status='COMPONENT_AUDIT_COMPLETE_NO_ROW_CREDIT',headline='AspisR1.RPx_Deployed.deployed',target_established=False,authoritative_credit=False,closed_rows=[],baseline_counts=dict(CLOSED=553,QUALIFIED=0,OPEN=46),budget=dict(kani_used=len(ks),kani_limit=70,lean_support_used=len(ls),lean_support_limit=120,extraction_used=0,extraction_limit=0,combined_invocations=len(records),combined_limit=190),new_proof_modules=len(mods['modules']),new_top_theorems=len(mods['roots']),combined_import=dict(attempt='NKQ_L071',exit=0,axiom_prints=55),full_combined_audits=1,nfx_scan=dict(exit=0,modules=len(loaded),dangling=0,duplicate_owners=0,import_mismatches=0,cached_replicas=sum(len(x['cached_replicas'])for x in loaded)),raw_ax2=dict(entries=sum(seen.values()),unique_roots=len(seen),standard_axioms_only=True,mismatches=mismatches,actual_nonzero_retained=True,classification='Known inherited standard-only raw/collector disagreement retained; raw walk authoritative under standing ruling'),fixtures=dict(exit=0,positive=4,mutations=4),audit_groups=groups,predecessor_comparison=comparison,compressed_reachable_files= compression_count,resource=dict(peak_rss_kib=max(int(r['peak_rss_kib']or 0)for r in records),swaps=0,scopes='MemoryHigh=6G MemoryMax=8G MemorySwapMax=0 TasksMax=64; serial',own_cargo_target='/home/dombarker/project-offloads/codex-cx-tx1-driver-20261108/NKQ_target'),trust='unchanged; option-A semantic transport reclassification, no added/removed trust',remaining='NKQ_REMAINING.md')
(E/'NKQ_AUDIT.json').write_text(json.dumps(status,indent=1)+'\n');print(json.dumps({k:status[k]for k in ['status','budget','new_proof_modules','new_top_theorems','resource']}))
