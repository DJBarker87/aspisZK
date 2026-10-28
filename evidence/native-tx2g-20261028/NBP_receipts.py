from pathlib import Path
import json,hashlib,re,subprocess
import sys
sys.dont_write_bytecode=True
from NBP_patch_sources import pieces
E=Path(__file__).resolve().parent
parts=pieces(E)
records=[];issues=[]
for p in sorted(E.glob('NBP_[KL]*/receipt.json')):
 r=json.loads(p.read_text());a=r['attempt'];kind=r['kind'];records.append(dict(attempt=a,kind=kind,target=r.get('module',r['command']),exit=r['exit_status'],wall=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps'],revision=r['source_revision'],source_hashes=r['source_hashes'],axioms=r['print_axioms']))
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},a
 assert str(r['swaps'])=='0',a
 ad=json.loads((E/(a+'-reservation.json')).read_text());assert ad['allowed'] is True,a
 if kind=='kani':
  graph=json.loads((E/(a+'-graph-check.json')).read_text());assert graph['graph_matches_frozen'],a
  lock=(E/(a+'-lock-after.log')).read_text().strip();assert lock==graph['lock_sha256']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef',a
  assert r['env']['CARGO_NET_OFFLINE']=='true' and r['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3',a
  assert '--locked' not in r['command'],a
 else:
  assert '-M7000' in r['command'],a
  if r['exit_status']==0:
   for audit in r['print_axioms']:
    if 'sorryAx' in audit or any(x.strip() not in ['propext','Classical.choice','Quot.sound'] for x in re.search(r'\[([^\]]*)\]',audit).group(1).split(',') if x.strip()) if '[' in audit else False:issues.append([a,audit])
 for name,sha in r['source_hashes'].items():
  q=p.parent/'sources'/name
  if q.is_file():data=q.read_bytes()
  else:
   assert kind=='kani'
   name=name.removeprefix('NBP_src/');number=int(a[-3:])
   if name.endswith('/NBP_error.rs'):
    data=parts['error']
    if number>=2:data+=parts['components']
    if number==40:data+=parts['forward']
   elif name.endswith('/NBP_codecs.rs'):
    data=parts['statement']
    if number>=30:data+=parts['statement2']
    if number>=31:data+=parts['payments']
   elif name.endswith('/NBP_filled.rs'):data=parts['filled']
   else:
    data=subprocess.check_output(['git','show','4bb3b3f5:'+name])
    if name=='programs/r1-cost-probe/src/lib.rs':data+=b'\n#[cfg(kani)]\nmod NBP_error;\n'
    elif name=='crates/aspis-statement/src/pool_v1/payment_relation.rs':data+=b'\n#[cfg(kani)]\nmod NBP_codecs;\n'
    elif name=='crates/aspis-core/src/r0/heap.rs':data+=b'\n#[cfg(kani)]\nmod NBP_filled;\n'
  assert hashlib.sha256(data).hexdigest()==sha,(a,name)

out=dict(lean=sum(r['kind']=='lean' for r in records),kani=sum(r['kind']=='kani' for r in records),kani_pass=sum(r['kind']=='kani' and r['exit']==0 for r in records),accepted_axiom_issues=issues,records=records)
assert out['lean']<=100 and out['kani']<=40 and not issues
(E/'NBP_VERIFICATION.json').write_text(json.dumps(out,indent=2)+'\n')
print({k:v for k,v in out.items() if k!='records'})
