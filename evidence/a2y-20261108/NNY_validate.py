"""Validate owned receipts; no prover or shared infrastructure changes."""
from pathlib import Path
import hashlib,json,re
E=Path(__file__).resolve().parent
accepted={};attempts=[];pins={}
for p in sorted(E.glob('NNY_L*/receipt.json')):
 r=json.loads(p.read_text());a=r['attempt'];c=json.loads((E/(a+'.json')).read_text())
 assert c['timeout']==180
 assert '-M7000' in c['command'] and '-j1' in c['command'] and '-DElab.async=false' in c['command']
 ad=json.loads((E/(a+'-admission.json')).read_text());assert ad['exit']==0 and ad['reservation']['allowed'] is True
 assert json.loads((E/(a+'-disk-0.json')).read_text())['free']>=40_000_000_000
 for key in ['exit_status','wall_seconds','peak_rss_kib','swaps','source_revision']:assert key in r,(a,key)
 assert int(r['swaps'])==0
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},a
 checks=[json.loads(x) for x in (E/'NNY_ATTEMPTS.jsonl').read_text().splitlines()]
 share=[x for x in checks if x.get('attempt')==a and x.get('event')=='share_check']
 assert share and share[-1]['host']['count']<6,a
 for src in c['sources']:
  f=p.parent/'sources'/src
  assert hashlib.sha256(f.read_bytes()).hexdigest()==r['source_hashes'][src],(a,src)

 for n,v in c['deps_fingerprint']['selected_objects'].items():
  if n in pins:assert pins[n]==v
  pins[n]=v
 out=(p.parent/'stdout.log').read_text();ax=[x for x in out.splitlines() if 'depends on axioms' in x or 'does not depend on any axioms' in x]
 if r['exit_status']==0:
  assert not re.search(r'\b(sorryAx|error:|error\()',out),a
  for x in ax:
   if 'depends on axioms:' in x: assert set(re.search(r'\[([^]]*)\]',x).group(1).split(', '))<={'propext','Classical.choice','Quot.sound'}
  for src in c['sources']:
   psrc=p.parent/'sources'/src
   assert psrc.is_file(),(a,src)
   if psrc.suffix=='.lean':
    assert not re.search(r'\b(sorry|axiom|admit|native_decide)\b|set_option\s+(maxHeartbeats|maxRecDepth)',psrc.read_text())
    name=psrc.stem;live=E/(name+'.lean')
    if live.exists() and live.read_bytes()==psrc.read_bytes():accepted[name]=a
 attempts.append({k:r[k] for k in ['attempt','module','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision']}|{'axioms':ax,'source_hashes':r['source_hashes'],'deps_fingerprint_sha256':hashlib.sha256(json.dumps(c['deps_fingerprint'],sort_keys=True).encode()).hexdigest(),'command':c['command']})
assert len(attempts)<=30
(E/'NNY_COMPILE.tsv').write_text('attempt\tmodule\texit\twall_seconds\tpeak_rss_kib\tswaps\tsource_revision\taxioms\tsource_hashes\tdeps_fingerprint_sha256\tcommand\n'+''.join('\t'.join(str(x[k]).replace('\n',' ') for k in ['attempt','module','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','axioms','source_hashes','deps_fingerprint_sha256','command'])+'\n' for x in attempts))
(E/'NNY_IMPORTED_PINS.json').write_text(json.dumps(pins,indent=2)+'\n')
(E/'NNY_VALIDATION.json').write_text(json.dumps({'scopes':len(attempts),'accepted_current_modules':accepted,'Kani':0,'extraction':0,'source_sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in E.glob('NNY_*.lean')}},indent=2)+'\n')
print(json.dumps({'scopes':len(attempts),'accepted_current_modules':accepted}))
