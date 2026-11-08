"""Read-only validation of owned run-5b receipts and retained source snapshots."""
from pathlib import Path
import hashlib,json,re,lzma
E=Path(__file__).resolve().parent
caps={'T1':14,'T2':16,'T3':14,'T4':20,'T5':6,'T6':2,'T7':6}
def step(i):
 for n,lo,hi in [('T1',843,853),('T2',854,859),('T3',860,873),('T4',874,893),('T5',894,899),('T6',900,901),('T7',902,999)]:
  if lo<=i<=hi:return n
allowed={'propext','Classical.choice','Quot.sound'}
rows=[];counts={n:0 for n in caps};pins={};latest={};roots={}
for p in sorted(E.glob('NNH_L[0-9][0-9][0-9]/receipt.json')):
 i=int(p.parent.name[-3:])
 if i<843:continue
 r=json.loads(p.read_text());a=r['attempt'];counts[step(i)]+=1
 for k in ['module','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','print_axioms','source_hashes','deps_fingerprint']:
  assert k in r,(a,k)
 assert r['kind']=='lean' and '-j1' in r['command'] and '-M7000' in r['command'] and '-DElab.async=false' in r['command'],a
 assert 'v4.32.0' in r['command'][0],a
 assert {k:str(v) for k,v in r['limits'].items()}=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},a
 assert str(r['swaps'])=='0',a
 ad=json.loads((E/(a+'-admission.json')).read_text());assert ad['exit']==0 and ad['reservation']['allowed'] is True,a
 disks=[json.loads(z.read_text()) for z in E.glob(a+'-disk-*.json')];assert disks and disks[-1]['free']>=40_000_000_000,a
 shares=[json.loads(z) for z in (E/'NNH_ATTEMPTS.jsonl').read_text().splitlines() if json.loads(z).get('attempt')==a and json.loads(z).get('event')=='share_check']
 assert shares and shares[-1]['host']['count']<6,a
 for name,sha in r['source_hashes'].items():
  f=p.parent/'sources'/name;assert f.is_file() and hashlib.sha256(f.read_bytes()).hexdigest()==sha,(a,name)
 if r['exit_status']==0:
  for line in r['print_axioms']:
   if 'depends on axioms:' in line:
    found={v.strip() for v in line.split('[',1)[1].split(']',1)[0].split(',') if v.strip()}
    assert found<=allowed,(a,line)
   m=re.match(r"'([^']+)'",line)
   if m:roots[m[1]]={'attempt':a,'axioms':line}
  latest[r['module']]=r
 for path,pin in r['deps_fingerprint']['selected_objects'].items():
  pins.setdefault(path,set()).add(pin['sha256'])
 rows.append({k:r[k] for k in ['attempt','module','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','print_axioms']})
assert len(rows)<=76 and all(counts[k]<=caps[k] for k in counts),(len(rows),counts)
for m,r in latest.items():
 f=E/(m+'.lean')
 assert f.is_file() and hashlib.sha256(f.read_bytes()).hexdigest()==r['source_hashes']['NNH_generated/'+m+'.lean'],m
 assert not re.search(r'\b(sorry|admit|native_decide)\b|^\s*axiom\b|set_option\s+(maxRecDepth|maxHeartbeats)',f.read_text(),re.M),m
assert not [str(f) for f in E.rglob('*') if f.is_file() and f.stat().st_size>20_000_000]
report={'actual_scopes':len(rows),'step_scopes':counts,'passes':sum(r['exit_status']==0 for r in rows),'receipt_validation':'PASS','accepted_root_axioms':roots,'results':rows,'imported_pin_paths':len(pins),'pin_variants':sum(len(x) for x in pins.values()),'not_launched':['NNH_L902'],'not_release_replay':True}
(E/'NNH_RUN5B_VALIDATION.json').write_text(json.dumps(report,indent=2)+'\n')
raw=json.dumps({k:sorted(v) for k,v in sorted(pins.items())},indent=2).encode();(E/'NNH_RUN5B_IMPORTED_PINS.json.xz').write_bytes(lzma.compress(raw,preset=6));(E/'NNH_RUN5B_IMPORTED_PINS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
print(json.dumps({k:report[k] for k in ['actual_scopes','step_scopes','passes','receipt_validation','imported_pin_paths','pin_variants']}))
