from pathlib import Path
import json,lzma,hashlib,subprocess
E=Path(__file__).resolve().parent
read=lambda p:p.read_bytes() if p.exists() else lzma.decompress(p.with_suffix(p.suffix+'.xz').read_bytes())
runs=json.loads((E/'runs.json').read_text());issues=[];starts=[];receipts={}
for run in runs:
 n=run['id'];D=E/'host'/n
 if not (D/'receipt.json').exists():issues.append(n+': missing receipt');continue
 rec=json.loads((D/'receipt.json').read_text());receipts[n]=rec
 for stage in ['admission','barrier']:
  a=json.loads((D/(stage+'.json')).read_text())
  if a.get('allowed') is not True:issues.append(n+': denied '+stage)
 limits=rec['limits']
 if list(limits.values())!=[str(6*2**30),str(8*2**30),'0','64']:issues.append(n+': limits')
 if rec['swap']!=0 or rec['cgroup_swap_peak_bytes']!='0':issues.append(n+': swap')
 identity=json.loads((D/'identity.json').read_text())
 if not all(x['match'] for x in identity['sources']) or not all(x['match'] for x in identity['tools'].values()):issues.append(n+': identity')
 starts.append((json.loads((D/'STARTED.json').read_text())['epoch'],n))
 raw=list(D.glob('cbmc-*.json'))+list(D.glob('cbmc-*.json.xz'))
 raw=[p for p in raw if not p.name.endswith('-command.json')]
 if not raw:issues.append(n+': missing raw CBMC trace/result')
 for p in raw:
  d=json.loads(lzma.decompress(p.read_bytes()) if p.suffix=='.xz' else p.read_bytes())
  for o in d:
   for prop in o.get('result',[]):
    if prop.get('status')=='FAILURE' and prop.get('sourceLocation',{}).get('propertyClass')!='reachability_check' and not prop.get('trace'):issues.append(n+': missing failure trace')
 si=json.loads((D/'symbols-index.json').read_text())
 if n=='K93512':si=json.loads((E/'host/K93502/symbols-index.json').read_text());records=[x for x in si['records'] if 'K93512' in x.get('command_receipt','')]
 else:records=si['records']
 if not records:issues.append(n+': missing symbols')
 if any(x['symbols_exit']!=0 for x in records):issues.append(n+': symbols error')
 for x in si['records']:
  p=(E/'host/K93502' if n=='K93512' else D)/x['symbols']
  if hashlib.sha256(lzma.decompress(p.read_bytes())).hexdigest()!=x['symbols_raw_sha256']:issues.append(n+': symbol hash')
starts.sort();gaps=[{'from':a[1],'to':b[1],'seconds':b[0]-a[0]}for a,b in zip(starts,starts[1:])]
if any(x['seconds']<180 for x in gaps):issues.append('launch gap below 180')
for p in E.rglob('*.sha256'):
 text=p.read_text().split();q=Path(str(p).removesuffix('.sha256')+'.xz')
 if q.exists() and hashlib.sha256(lzma.decompress(q.read_bytes())).hexdigest()!=text[0]:issues.append(str(p.relative_to(E))+': archive hash')
large=[str(p.relative_to(E))for p in E.rglob('*') if p.is_file() and p.stat().st_size>20*1024*1024]
if large:issues.append('over20MB: '+str(large))
changed=sorted(set(subprocess.check_output(['git','diff','--name-only','670416be996','--']).decode().splitlines()+subprocess.check_output(['git','ls-files','--others','--exclude-standard',str(E)]).decode().splitlines()))
if any(not p.startswith('evidence/k3-audit-20261030/k4trace/') for p in changed):issues.append('path boundary')
out={'status':'PASS' if not issues else 'FAIL','issues':issues,'planned_replays':len(runs),'received_replays':len(receipts),'launch_gaps':gaps,'peak_rss_kib':max([r['peak_rss_kib']for r in receipts.values()]or[0]),'sum_wall_seconds':sum(r['wall_seconds']for r in receipts.values()),'swap':0,'Lean':0,'axioms':'N/A: 0 Lean','path_changes':changed,'over20MB':large}
(E/'validation.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k!='path_changes'},indent=2))
