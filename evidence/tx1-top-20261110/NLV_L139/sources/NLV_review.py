from pathlib import Path
import json,re,hashlib
B=Path.cwd();H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((B/'NLV_MODULES.json').read_text());expected=set(json.loads((B/'NLV_AUDIT_ROOTS.json').read_text())['roots']);results=[]
for p in sorted((B/'NLV_audit').glob('proof*/proof*.json')):results+=json.loads(p.read_text())['results']
assert len(results)==len(expected)and{r['root']for r in results}==expected
std={'propext','Classical.choice','Quot.sound'};assert all(set(r['walked_axioms'])<=std for r in results)
wrong=[r for r in results if not r['equal']];known={'NHC_DecodeModel.decoder_error','AspisR1.NKR_ScheduleExt.transition'}
assert{r['root']for r in wrong}<=known,wrong
scan=[json.loads(l)for l in(B/'NLV_LOADED_scan.jsonl').read_text().splitlines()];assert all(not r['dangling']and not r['duplicate_owners']and r['imports_match']for r in scan)
versions={H(p):p.read_text()for p in B.glob('NLV_L*/sources/NLV_native.rs.txt')};p=B/'NLV_native.rs.txt';versions[H(p)]=p.read_text()
positives=[];negatives=[];excluded=[]
for n in range(1,41):
 a=f'NLV_K{n:03d}';r=json.loads((B/a/'receipt.json').read_text());out=(B/a/'stdout.log').read_text()
 if n in [1,2,7]:excluded.append(dict(attempt=a,exit=r['exit_status'],reason='compile-only'if n==1 else'retired90s timeout'));continue
 if r['exit_status']==0:
  assert 'VERIFICATION:- SUCCESSFUL'in out;positives.append(a)
 else:
  assert r['exit_status']==1 and'VERIFICATION:- FAILED'in out and re.search(r'\*\*\s+1 of \d+ failed',out)
  pins=json.loads((B/a/'sources/NLV_SOURCE_PINS.json').read_text());h=pins['crates/aspis-r1-cost-probe/src/NLV_native.rs'];assert h in versions,(a,h)
  source=versions[h];lines=[j+1 for j,l in enumerate(source.splitlines())if'assert!(!good,'in l]
  m=re.search(r'File: "crates/aspis-r1-cost-probe/src/NLV_native.rs", line (\d+), in ([^\n]+)',out)
  assert m and int(m[1])in lines and m[2].strip().split('::')[-1]in ['prefix_check','prefix_window','small_window','check'],a
  negatives.append(a)
assert len(positives)==19 and len(negatives)==18
own=set(manifest['roots']);assert own<={r['root']for r in results}
assert all(r['equal']for r in results if r['root']in own)
res=dict(status='SUPPORT AUDIT COMPLETE; TARGET NOT ESTABLISHED',modules=len(scan),own_modules=len(manifest['modules']),own_roots=len(own),required_roots=len(expected),raw_axioms_standard=True,inherited_collector_disagreements=wrong,native=dict(positives=positives,matched_negative_failures=negatives,excluded=excluded,row_credit=0),closed_rows=[],root_emitted=False,full_resource087_provided=False,full_physical094_producer=False)
(B/'NLV_REVIEW.json').write_text(json.dumps(res,indent=2));print(json.dumps({k:res[k]for k in ['status','modules','own_modules','own_roots','required_roots','raw_axioms_standard','root_emitted']}))
